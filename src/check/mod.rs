/*!

# The `check` module

This module contains utilities and structures
to guarantee the validity of the input AST and
transform it into output, specialized IR, which
removes the concept of namespaces and inlines
all names.

Note: The `Act`- prefix here is used to denote
that an item is a type alias of another
type which is the one actually used.

- For example: for namespaces, we use
`Rc<RefCell<Namespace>>`, or `ActNamespace`
instead of using `Namespace` in the
implementation directly.

*/

mod ctx;
pub mod hir;
mod namespaces;
mod scopes;

use std::{
    cell::{Ref, RefCell}, collections::HashMap, ops::{BitAnd, BitAndAssign}, rc::Rc
};

use ansi_term::Color;
use derive_getters::Getters;
use derive_new::new;
use either::Either;

use crate::{
    ast::{
        expr::{
            AsReferenceExpr, AssignmentExpr, BinaryExpr, BinaryOp, CallExpr, Conditional,
            Expr, LiteralExpr, ReturnExpr, WhileLoop,
        }, generics::Generic, matcher::{Case, Pattern, Switch}, tdecl::{Struct, SumVariant, TypeDecl, UserType}, typing::{NameIndex, PrimType, Type, TypeBits}, Block, Collection, Decl, FunctionDecl, Identifier, IntLit, Loc, Mutability, NamespaceDecl, Prototype, Receiver
    },
    check::{hir::{expr::HIRLiteralExpr, HIRArgument}, namespaces::Member},
};

use self::{
    ctx::Context,
    hir::{
        expr::{
            BinOpType, HIRAsReferenceExpr, HIRAssignmentExpr, HIRBinaryExpr, HIRCallExpr,
            HIRConditional, HIRExpr, HIRReturnExpr, HIRWhileLoop,
        }, matcher::{HIRCase, HIRPattern, HIRSwitch}, typing::HIRType, HIRBlock, HIRDecl, HIRFunctionDecl, HIRPrototype
    },
    namespaces::{AddMemberError, WeakNamespace},
    scopes::Variable,
};

use hir::HighLevelIR;

#[derive(Debug, PartialEq)]
/// The state of the expression evaluator.
///
/// Precisely what exactly it is evaluating.
pub enum ExprState {
    /// A statement.
    IsStmt,
    /// An expression.
    IsExpr,
    /// The left hand side of an assignment
    IsAssignmentLhs,
}

#[derive(Debug, Getters)]
/// Data about a function within the compiler.
///
/// This includes its signature and actual name,
/// as we may use this
pub struct Function {
    /// The signature of the function.
    proto: Prototype,
    /// The namespace where the function
    /// is defined.
    ///
    /// This is useful for name mangling
    /// and namespace inlining.
    parent: WeakNamespace,
}

#[derive(Debug, Getters)]
/// Data about a generic function within the compiler.
///
/// This includes its signature and actual name,
/// as we may use this
pub struct GenericFunction {
    /// The definition of the function.
    decl: FunctionDecl,
    /// The instantiated types.
    instantiated: Vec<(Vec<Type>, GenericFunction, HIRPrototype, Prototype)>,
    /// The namespace where the function
    /// is defined.
    ///
    /// This is useful for name mangling
    /// and namespace inlining.
    parent: WeakNamespace,
}

/// The function type which is actually used.
///
/// We use `Rc<RefCell<Function>>` here instead of `Function`
/// because scopes reference their father function.
pub type ActFunction = Rc<RefCell<Function>>;

/// The generic function type which is actually used.
///
/// We use `Rc<RefCell<Function>>` here instead of `Function`
/// because scopes reference their father function.
pub type ActGenericFunction = Rc<RefCell<GenericFunction>>;

impl Function {
    /// Creates an actual function.
    pub fn new(proto: Prototype, parent: WeakNamespace) -> ActFunction {
        Rc::new(RefCell::new(Function { proto, parent }))
    }

    /// Gets the full, mangled name
    /// of the function.
    pub fn full_name(&self, collection: &Collection) -> String {
        let mut parent_namespace_name = namespaces::full_name(
            &self
                .parent
                .upgrade()
                .expect("Parent namespace of function dropped before function did"),
            collection,
        );
        parent_namespace_name.push('.');
        parent_namespace_name += collection
            .get(self.proto.name().index())
            .expect("Bad function name");
        parent_namespace_name
    }
}

impl GenericFunction {
    /// Creates an actual function.
    pub fn new(decl: FunctionDecl, parent: WeakNamespace) -> ActGenericFunction {
        Rc::new(RefCell::new(GenericFunction { decl, parent, instantiated: vec![] }))
    }

    /// Gets the full, mangled name
    /// of the function.
    pub fn full_name(&self, collection: &Collection) -> String {
        let mut parent_namespace_name = namespaces::full_name(
            &self
                .parent
                .upgrade()
                .expect("Parent namespace of function dropped before function did"),
            collection,
        );
        parent_namespace_name.push('.');
        parent_namespace_name += collection
            .get(self.decl().prototype.name().index())
            .expect("Bad function name");
        parent_namespace_name
    }
}

#[derive(Debug, new)]
/// Data about a user type in the context.
pub struct CtxUserType {
    /// The actual user defined type.
    ty: UserType,
    /// The methods defined for this user
    /// type (functions with this as their
    /// receiver).
    methods: HashMap<NameIndex, ActFunction>,
    /// The namespace where the function
    /// is defined.
    ///
    /// This is useful for name mangling
    /// and namespace inlining.
    parent: WeakNamespace,
}

pub type ActCtxUserType = Rc<RefCell<CtxUserType>>;

/// The [`Checker`] structure is used to validate the
/// input AST and generate output HIR, inlining
/// namespaces and other things.
pub struct Checker {
    /// The collection of names.
    collection: Collection,
    /// The output high level IR.
    out: Vec<HighLevelIR>,
    /// The context of this.
    ctx: Context,
    /// The errors generated during
    /// type checking.
    errors: Vec<CheckerError>,
    /// The warnings generated during
    /// type checking.
    warnings: Vec<WarningOrError>,
}

impl Checker {
    /// Constructs a new `Checker`.
    pub fn new(mut collection: Collection) -> Self {
        let ctx = Context::new(&mut collection);
        Self {
            collection,
            out: Vec::new(),
            ctx,
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    pub fn errors(&self) -> &[CheckerError] {
        self.errors.as_slice()
    }

    pub fn warnings(&self) -> &[WarningOrError] {
        self.warnings.as_slice()
    }

    pub fn collection(&self) -> &Collection {
        &self.collection
    }

    /// Collects all names.
    pub fn collect(&mut self, program: &[Decl]) {
        for decl in program {
            self.collect_decl(decl)
        }
    }

    /// Collects one single declaration
    fn collect_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::FunctionDecl(function_decl) => {
                let fdecl = function_decl;

                if let Some(receiver) = &fdecl.prototype.receiver {
                    if let Type::NamedType(named) = &**receiver.ty() {
                        self.collect_method(
                            named,
                            function_decl,
                        )
                    } else if let Type::Pointer { pointee, .. } = &**receiver.ty() {
                        if let Type::NamedType(named) = &**pointee {
                            self.collect_method(
                                named,
                                function_decl,
                            )
                        } else {
                            self.add_error(
                                CheckerError::InvalidTypeAsReceiver(function_decl.prototype.name.clone(), (**receiver.ty()).clone())
                            );
                        }
                    } else {
                        self.add_error(
                            CheckerError::InvalidTypeAsReceiver(function_decl.prototype.name.clone(), (**receiver.ty()).clone())
                        );
                    }
                } else if fdecl.prototype.generics().is_none() {
                    // check if it already existed and if yes
                    // add the error
                    if let Err(error) = self
                        .ctx
                        .insert_function(fdecl.prototype.name().index(), fdecl.prototype.clone())
                    {
                        self.add_error(CheckerError::AddMember(
                            fdecl.prototype.name().loc().clone(),
                            error,
                        ));
                    }
                } else {
                    // check if it already existed and if yes
                    // add the error
                    if let Err(error) = self
                        .ctx
                        .insert_generic_function(fdecl.prototype.name().index(), fdecl.clone())
                    {
                        self.add_error(CheckerError::AddMember(
                            fdecl.prototype.name().loc().clone(),
                            error,
                        ));
                    }
                }

            }
            Decl::TypeDecl(ty) => {
                let TypeDecl { name, ty, .. } = ty;

                if let Err(error) = self
                    .ctx
                    .insert_type(name.index(), ty.clone()) {
                        self.add_error(CheckerError::AddMember(
                            name.loc().clone(),
                            error
                        ))
                    }
            }
            Decl::NamespaceDecl(namespace) => {
                self.collect_namespace_impl(namespace, true);
            }
        }
    }

    fn collect_method(
        &mut self,
        named: &Identifier,
        function_decl: &FunctionDecl,
    ) {
        let fdecl = function_decl;

        if let Some(Member::Type(ty)) = self.ctx.lookup_member(&named.index()) {
            match self.ctx.insert_function(function_decl.prototype.name.index(), function_decl.prototype.clone()) {
                Ok(f) => match f {
                    Member::Function(f) => {
                        if let Some(_) = ty.borrow_mut()
                            .methods
                            .insert(
                                function_decl.prototype.name.index(),
                                Rc::clone(&f)
                            ) {
                                self.add_error(
                                    CheckerError::MethodRedefinition {
                                        aggr: named.clone(),
                                        name: function_decl.prototype.name.clone(),
                                    }
                                )
                            }
                    },
                    _ => unreachable!(),
                }
                Err(error) => {
                    self.add_error(CheckerError::AddMember(
                        fdecl.prototype.name().loc().clone(),
                        error,
                    ));
                }
            }
        } else {
            self.add_error(
                CheckerError::TypeMustBeDefinedAtTimeOfDefinitionForReceiver {
                    function: function_decl.prototype.name.clone(),
                    name: named.clone(),
                }
            );
        }
    }

    fn collect_namespace_impl(
        &mut self,
        NamespaceDecl { name, decls, .. }: &NamespaceDecl,
        root: bool,
    ) {
        // start namespace
        if root {
            self.ctx.start_root_namespace(name.index());
        } else {
            self.ctx.start_child_namespace(name.index());
        }

        for decl in decls.iter() {
            if let Decl::NamespaceDecl(namespace_decl) = decl {
                self.collect_namespace_impl(namespace_decl, false);
            } else {
                self.collect_decl(decl);
            }
        }

        // close namespace
        self.ctx.end_namespace();
    }

    /// Verifies a whole program.
    pub fn pass_program(&mut self, program: &[Decl]) -> Vec<HIRDecl> {
        let mut output = vec![];

        for decl in program {
            if let Some(decl_hir) = self.pass_decl(decl) {
                output.extend(decl_hir);
            }
        }

        output
    }

    /// Verifies through a declaration.
    fn pass_decl(&mut self, decl: &Decl) -> Option<Vec<HIRDecl>> {
        match decl {
            Decl::FunctionDecl(function_decl) => {
                Some(vec![self.pass_function_decl(function_decl)?])
            }
            Decl::TypeDecl(type_decl) => {
                self.pass_type_decl(type_decl);
                // nothing is generated for this
                None
            }
            Decl::NamespaceDecl(namespace_decl) => Some(self.pass_namespace_decl(namespace_decl)),
        }
    }

    /// Verifies the declaration of a function.
    fn pass_function_decl(
        &mut self,
        FunctionDecl {
            attrs,
            def,
            prototype,
            block,
        }: &FunctionDecl,
    ) -> Option<HIRDecl> {
        // Note: name collision checks were done in the name collection phase

        // generic functions are checked at instantiation
        if prototype.generics().is_some() {
            return None;
        }
        
        let function = match self.ctx.lookup_member(&prototype.name().index()) {
            Some(Member::Function(func)) => func,
            _ => if let Member::Function(f) = self.ctx.insert_function(prototype.name.index(), prototype.clone()).unwrap() {
                f
            } else {
                unreachable!()
            },  
        };

        // verify the prototype
        let proto = self.pass_proto(prototype, &function);

        // set current function
        self.ctx.set_current_function(function);

        // starts the processing of the block
        self.ctx
            .add_function_scope(prototype.receiver().as_ref(), prototype.arguments(), *prototype.unsafety());

        let (reachability, hirblock) = self.pass_block(block, false)?;

        if reachability.reachable() {
            if **prototype.return_type() != Type::Void {
                self.add_error(CheckerError::DoesNotRetInAllPathsButMust {
                    loc: def.clone(),
                    expected_ty: (**prototype.return_type()).clone(),
                });
            }
        }

        // pop a scope
        self.ctx.pop_scope();

        Some(HIRDecl::FunctionDecl(HIRFunctionDecl::new(
            attrs.clone(),
            proto?,
            hirblock,
        )))
    }

    /// Verifies the declaration of a type.
    fn pass_type_decl(&mut self, ty_decl: &TypeDecl) {
        let TypeDecl { type_kw: _, name, equal_sign: _, ty } = ty_decl;

        match ty {
            UserType::Alias(alias) => {
                self.pass_ty(alias.clone());
            },
            UserType::Struct(Struct { fields })
            | UserType::Union(fields) => {
                let mut occurred_fields = vec![];

                for (field_name, field_ty) in fields.iter() {
                    if occurred_fields.contains(&field_name.index()) {
                        self.add_error(
                            CheckerError::StructFieldRedefinition {
                                name: name.clone(),
                                field: field_name.clone(),
                                for_: if matches!(ty, UserType::Struct(_)) {
                                    "struct"
                                } else {
                                    "union"
                                }
                            }
                        );
                    } else {
                        occurred_fields.push(field_name.index());
                        self.pass_ty(field_ty.clone());
                    }
                }
            }
            UserType::Sum(sum_ty) => {
                // store info about the discriminants
                let mut appeared_discriminants: Vec<(u64, Identifier)> = vec![];

                for SumVariant {
                    parent,
                    name,
                    discriminant,
                    aggregate_fields
                } in sum_ty {
                    // check for discriminant index repetition
                    let discr_value = discriminant.2;
                    if let Some((_, before)) = appeared_discriminants.iter().find(|value| value.0 == discr_value) {
                        // index repeated
                        self.add_error(
                            CheckerError::RepeatedSumTyDiscriminant {
                                sum_ty: parent.clone(),
                                variant: name.clone(),
                                before: before.clone(),
                                discriminant: discr_value,
                            }
                        );
                    } else {
                        appeared_discriminants.push((discr_value, name.clone()));
                    }

                    if let Some(fields) = aggregate_fields {
                        // check its fields now, if any
                        let mut occurred_fields = vec![];
                        for (field_name, field_ty) in fields.fields().iter() {
                            if occurred_fields.contains(&field_name.index()) {
                                self.add_error(
                                    CheckerError::StructFieldRedefinition {
                                        name: name.clone(),
                                        field: field_name.clone(),
                                        for_: "sum type variant",
                                    }
                                );
                            } else {
                                occurred_fields.push(field_name.index());
                                self.pass_ty(field_ty.clone());
                            }
                        }
                    }
                }
            }
        }
    }

    /// Flattens the declaration of a namespace.
    fn pass_namespace_decl(&mut self, namespace_decl: &NamespaceDecl) -> Vec<HIRDecl> {
        self.pass_namespace_decl_impl(namespace_decl, true)
    }

    /// The implementation of the namespace declaration.
    fn pass_namespace_decl_impl(
        &mut self,
        namespace_decl: &NamespaceDecl,
        root: bool,
    ) -> Vec<HIRDecl> {
        let mut output = vec![];

        if root {
            self.ctx.restart_root_namespace(namespace_decl.name.1)
        } else {
            self.ctx.restart_child_namespace(namespace_decl.name.1)
        }
        .unwrap();

        for decl in namespace_decl.decls.iter() {
            if let Decl::NamespaceDecl(decl) = decl {
                output.extend(self.pass_namespace_decl_impl(decl, false));
            } else {
                if let Some(outputted) = self.pass_decl(decl) {
                    output.extend(outputted);
                }
            }
        }

        self.ctx.end_namespace();

        output
    }

    /// Passes through a block and returns if
    /// anything is reachable after it.
    fn pass_block(&mut self, block: &Block, add_scope: bool) -> Option<(Reachability, HIRBlock)> {
        let mut reachable = Reachability::Reachable;
        let mut hirblock_contents = vec![];
        let mut altered = false;

        if add_scope {
            self.ctx.add_normal_scope(false);
        }

        for expr in block.stmts().iter() {
            if let Reachability::Unreachable = reachable {
                // unreachable code found
                self.add_error(CheckerError::StmtIsUnreachable(expr.loc()));
                break;
            }
            match self.pass_expr(expr, ExprState::IsStmt, None) {
                Some((_, reachability, hirexpr)) => {
                    if let Reachability::Unreachable = reachability {
                        reachable = Reachability::Unreachable
                    }
                    hirblock_contents.push(hirexpr);
                }
                None => {
                    altered = true;
                }
            }
        }

        if add_scope {
            self.ctx.pop_scope();
        }

        if !altered {
            Some((reachable, HIRBlock::new(hirblock_contents)))
        } else {
            None
        }
    }

    /// Validates a prototype.
    fn pass_proto(&mut self, proto: &Prototype, func: &ActFunction) -> Option<HIRPrototype> {
        let Prototype {
            arguments,
            return_type,
            ..
        } = proto;

        let mut error = false;

        let mut new_arguments = vec![];

        if let Some(receiver) = proto.receiver() {
            new_arguments.push(
                HIRArgument::new(
                    self.collection
                        .unwrap_get(receiver.receiver_name().1)
                        .to_string(),
                    self.pass_ty((**receiver.ty()).clone())?,
                )
            );
        }

        for argument in arguments {
            if let Some(argument_ty) = self.pass_ty(argument.ty.clone()) {
                new_arguments.push(HIRArgument::new(
                    self.collection
                        .unwrap_get(argument.name.index())
                        .to_string(),
                    argument_ty,
                ));
            } else {
                error = true;
            }
        }

        let return_type = Box::new(self.pass_ty((&**return_type).clone())?);

        let new_name = func.borrow().full_name(&self.collection);

        if error {
            None
        } else {
            Some(HIRPrototype {
                name: new_name,
                arguments: new_arguments,
                return_type,
            })
        }
    }

    /// Passes a single type.
    fn pass_ty(&mut self, ty: Type) -> Option<HIRType> {
        match ty {
            Type::Primitive { loc, ty } => Some(HIRType::new_primitive(loc, ty)),
            Type::SizedArray {
                left_bracket,
                size,
                element_type,
                ..
            } => {
                // array of zero sized elements is not allowed
                if self.is_valueless_type(&element_type) {
                    self.add_error(CheckerError::ZeroSizedTypeArray(
                        left_bracket,
                        *element_type,
                    ));

                    None
                } else if size.1 {
                    self.add_error(CheckerError::NegativeSizedArray(size.0.clone(), size));

                    None
                } else {
                    let subtype = self.pass_ty(*element_type)?;

                    Some(HIRType::new_sized_array(size, Box::new(subtype)))
                }
            }
            Type::Tuple(t) => {
                // typecheck each field
                let mut hir_fields = vec![];
                for subtype in t.into_iter() {
                    hir_fields.push(self.pass_ty(subtype)?);
                }
                Some(self.struct_hir_ty_from_hir_fields(&hir_fields)?)
            }
            Type::Void => Some(HIRType::new_void()),
            Type::FunctionPointer(sig) => {
                let func = self.ctx.lookup_member(&sig.name().index())?;
                if let Member::Function(function) = func {
                    Some(HIRType::new_function_pointer(
                        self.pass_proto(&sig, &function)?,
                    ))
                } else {
                    None
                }
            }
            Type::Universe => Some(HIRType::new_universe()),
            Type::Pointer { pointee, mutability, lifetime: _ } => Some(HIRType::new_pointer(
                Box::new(self.pass_ty(*pointee)?),
                mutability.clone(),
            )),
            Type::NamedType(name) => {
                let member = self.ctx.lookup_member(&name.index())?;
                if let Member::Type(ty) = member {
                    match &ty.borrow().ty {
                        UserType::Alias(to) => {
                            self.pass_ty(to.clone())
                        }
                        UserType::Struct(Struct { fields }) => {
                            self.struct_hir_ty_from_fields(fields)
                        }
                        UserType::Sum(sum_ty) => {
                            let mut union_fields = vec![];
                            for variant in sum_ty.iter() {
                                match variant.aggregate_fields() {
                                    Some(sum_fields) => {
                                        // add this variant
                                        let mut hir_fields = Vec::with_capacity(sum_fields.fields().len());

                                        for (_, field_ty) in sum_fields.fields().iter(){ 
                                            hir_fields.push(self.pass_ty(field_ty.clone())?);
                                        }

                                        union_fields.push(HIRType::Struct(hir_fields).into_aligned(std::mem::size_of::<usize>()));
                                    }
                                    None => {},
                                }
                            }

                            let discriminant_type = HIRType::new_primitive(
                                Loc::default(),
                                PrimType::UInt(TypeBits::B64),
                            );
                            Some(HIRType::new_sum_type(
                                Box::new(discriminant_type),
                                union_fields,
                            ))
                        }
                        UserType::Union(fields) => {
                            let mut hir_fields = Vec::with_capacity(fields.len());

                            for (_, field_ty) in fields.iter(){ 
                                hir_fields.push(self.pass_ty(field_ty.clone())?);
                            }

                            Some(HIRType::Union(hir_fields))
                        }
                    }
                } else {
                    self.add_error(
                        CheckerError::NamedTypeNotFound(name)
                    );

                    None
                }
            }
            Type::Instantiated { .. } => {
                // TODO: Implement instantiated named types
                unimplemented!()
            }
        }
    }

    /// Converts a struct type into its HIR equivalent from its fields.
    fn struct_hir_ty_from_fields(&mut self, fields: &[(Identifier, Type)]) -> Option<HIRType> {
        let mut hir_fields = Vec::with_capacity(fields.len());

        for (_, field_ty) in fields.iter(){ 
            hir_fields.push(self.pass_ty(field_ty.clone())?);
        }

        Some(HIRType::Struct(hir_fields).into_aligned(std::mem::size_of::<usize>()))
    }

    /// Converts a struct type into its HIR equivalent from its fields.
    fn struct_hir_ty_from_hir_fields(&mut self, fields: &[HIRType]) -> Option<HIRType> {
        Some(HIRType::Struct(fields.to_vec()).into_aligned(std::mem::size_of::<usize>()))
    }

    /// Passes through an expression which gives out
    /// an error if the expression is unreachable.
    fn pass_reachable_expr(&mut self, expr: &Expr, state: ExprState, expected_type: Option<Type>) -> Option<(Type, HIRExpr)> {
        let res = self.pass_expr(expr, state, expected_type)?;

        if let Reachability::Unreachable = res.1 {
            self.add_error(CheckerError::UsingUnreachableExprAsVal(expr.loc()));

            None
        } else {
            Some((res.0, res.2))
        }
    }

    /// Validates an expression.
    fn pass_expr(
        &mut self,
        expr: &Expr,
        state: ExprState,
        expected_type: Option<Type>,
    ) -> Option<(Type, Reachability, HIRExpr)> {
        let prim: Option<(Type, HIRExpr)> = match expr {
            Expr::Let { mutable, loc_or_let, name, ty, eq, expr } => self.pass_let_expr(*mutable, loc_or_let, name, ty.as_ref(), eq, expr),
            Expr::AsReference(asref) => {
                if matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsStatement(
                        expr.loc(),
                        "taking lvalue reference of expression",
                    ));
                    None
                } else {
                    self.pass_asref_expr(asref, state)
                }
            }
            Expr::Literal(lit) => {
                if matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsStatement(
                        expr.loc(),
                        "literal expression",
                    ));
                    None
                } else {
                    self.pass_lit_expr(lit, expected_type)
                }
            }
            Expr::Dereference(deref, base) => {
                if matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsStatement(
                        expr.loc(),
                        "dereferencing expression",
                    ));
                    None
                } else {
                    self.pass_dereference_expr(deref, &base)
                }
            }
            Expr::InstantiateStruct(name, fields) => {
                if matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsStatement(
                        expr.loc(),
                        "instantiate struct expression",
                    ));
                    None
                } else {
                    self.pass_instantiate_struct(name, fields)
                }
            }
            Expr::GenericInstantiation(name, templates) => self.pass_generic_instantiation(name, templates),
            Expr::AccessProperty(base, dot, prop) => {
                self.pass_access_property(base, dot.clone(), prop)
                    .map(|v| (v.0, v.1))
            },
            Expr::MethodCall { base, name, params } => {
                self.pass_method_call(&base, name, &params)
            }
            Expr::Binary(binary) => {
                if matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsStatement(
                        expr.loc(),
                        "binary operation",
                    ));
                    None
                } else {
                    self.pass_bin_expr(binary)
                }
            }
            Expr::Call(call) => self.pass_call_expr(call),
            Expr::Variable(var) => {
                let is_being_initialized = matches!(state, ExprState::IsAssignmentLhs);
                match self.get_var(
                    var.loc(),
                    &var.index(),
                    is_being_initialized,
                    is_being_initialized,
                ) {
                    Some(var) => Some((var.0, var.1)),
                    None => {
                        self.add_error(CheckerError::UndefinedName(var.clone()));
                        None
                    }
                }
            }
            Expr::Assignment(assignment) => {
                if !matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsValue(
                        expr.loc(),
                        "assignment operation",
                    ));
                    None
                } else {
                    self.pass_assignment(assignment)
                }
            }
            Expr::Switch(switch) => {
                if !matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsValue(
                        expr.loc(),
                        "switch statement",
                    ));
                    None
                } else {
                    return self.pass_switch(switch)
                }
            }
            Expr::SlotDecl { mutability, name, ty } => {
                if !matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsValue(
                        expr.loc(),
                        "slot declaration ",
                    ));
                    None
                } else {
                    self.pass_slot_decl(name, ty, mutability)
                }
            }
            Expr::Return(r) => {
                if !matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsValue(
                        expr.loc(),
                        "return statement",
                    ));
                    None
                } else {
                    return self.pass_return_expr(r);
                }
            }
            Expr::Conditional(Conditional {
                if_kw,
                condition,
                then,
                else_part,
            }) => {
                if !matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsValue(
                        expr.loc(),
                        "conditional",
                    ));
                    None
                } else {
                    return self.pass_conditional(if_kw, condition, then, else_part.as_ref());
                }
            }
            Expr::WhileLoop(WhileLoop {
                while_kw,
                condition,
                block,
            }) => {
                if !matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsValue(
                        expr.loc(),
                        "while loop",
                    ));
                    None
                } else {
                    return self.pass_while_loop(while_kw, condition, block);
                }
            }
            Expr::Defer(defer_kw, subexpr) => {
                if !matches!(state, ExprState::IsStmt) {
                    self.add_error(CheckerError::InvalidExpressionAsValue(
                        defer_kw.clone(),
                        "defer statement",
                    ));
                    None
                } else {
                    let (_, subexpr_hir) = self.pass_reachable_expr(&subexpr, ExprState::IsExpr, None)?;
                    Some((Type::Void, HIRExpr::new_defer(Box::new(subexpr_hir))))
                }
            }
        };
        let prim_target = prim?;
        Some((prim_target.0, Reachability::Reachable, prim_target.1))
    }

    /// Verifies the validity of a while loop.
    fn pass_while_loop(
        &mut self,
        while_kw: &Loc,
        condition: &Expr,
        block: &Block,
    ) -> Option<(Type, Reachability, HIRExpr)> {
        // check condition
        let cond = self.pass_condition(condition)?;

        // check block
        let (reachability, hirblock) = self.pass_block(block, true)?;

        self.check_for_loop_loopability(while_kw, reachability.clone());

        Some((
            Type::new_void(),
            reachability,
            HIRExpr::WhileLoop(HIRWhileLoop {
                while_kw: while_kw.clone(),
                condition: Box::new(cond),
                block: hirblock,
            }),
        ))
    }

    /// Checks if a loop actually loops more than once.
    fn check_for_loop_loopability(&mut self, loc: &Loc, reachability: Reachability) {
        if reachability.unreachable() {
            // add warning if loop only executes once
            self.add_warning(WarningOrError::LoopOnlyExecutesOnce(loc.clone()));
        }
    }

    /// Verifies the validity of a conditional expression.
    fn pass_conditional(
        &mut self,
        if_kw: &Loc,
        condition: &Expr,
        then: &Block,
        else_part: Option<&(Loc, Block)>,
    ) -> Option<(Type, Reachability, HIRExpr)> {
        let cond = self.pass_condition(condition)?;
        if let Some(else_part) = else_part {
            // then code after this MIGHT be unreachable

            let (reachability_of_if, hir_if_block) = self.pass_block(then, false)?;
            let (reachability_of_else, hir_else_block) = self.pass_block(&else_part.1, false)?;
            let reachability_of_conditional = reachability_of_if & reachability_of_else;

            Some((
                Type::new_void(),
                reachability_of_conditional,
                HIRExpr::Conditional(HIRConditional {
                    if_kw: if_kw.clone(),
                    condition: Box::new(cond),
                    then: hir_if_block,
                    else_part: Some((else_part.0.clone(), hir_else_block)),
                }),
            ))
        } else {
            // code after this is surely reachable
            let (_, hir_if_block) = self.pass_block(then, true)?;

            Some((
                Type::new_void(),
                Reachability::Reachable,
                HIRExpr::Conditional(HIRConditional {
                    if_kw: if_kw.clone(),
                    condition: Box::new(cond),
                    then: hir_if_block,
                    else_part: None,
                }),
            ))
        }
    }

    /// Validates a condition.
    fn pass_condition(&mut self, condition: &Expr) -> Option<HIRExpr> {
        let (conditional_ty, hir_conditional) =
            self.pass_reachable_expr(condition, ExprState::IsExpr, None)?;

        if !matches!(
            conditional_ty,
            Type::Primitive {
                ty: PrimType::Bool,
                ..
            }
        ) {
            // Condition isn't of type 'bool'
            self.add_error(CheckerError::CondIsntBool(condition.loc(), conditional_ty));
        }

        Some(hir_conditional)
    }

    /// Validates an expression of taking an lvalue reference.
    fn pass_asref_expr(
        &mut self,
        expr: &AsReferenceExpr,
        state: ExprState,
    ) -> Option<(Type, HIRExpr)> {
        let AsReferenceExpr(ampersand, expr) = expr;
        match expr.as_ref() {
            Expr::AsReference(expr) => self.pass_asref_expr(expr, state),
            Expr::Variable(variable_name) => {
                // return a pointer to the specified type
                let set_init = matches!(state, ExprState::IsAssignmentLhs);
                let (var_ty, var_expr, var_mut, var_was_init, scope_index) = self.get_var(
                    variable_name.loc(),
                    &variable_name.index(),
                    set_init,
                    set_init,
                )?;
                if let ExprState::IsAssignmentLhs = state {
                    if !var_was_init {
                        // return mutable pointer if variable is not
                        // initialized
                        return Some((Type::new_pointer(Box::new(var_ty), Some(Loc::default()), Some(scope_index)), var_expr))
                    }
                }
                Some((Type::new_pointer(Box::new(var_ty), var_mut, Some(scope_index)), var_expr))
            }
            Expr::AccessProperty(base, dot, ident) => {
                let (ty, expr, lifetime) = self.pass_access_property(base, dot.clone(), ident)?;
                Some((Type::new_pointer(Box::new(ty), Some(Loc::default()), lifetime), expr))
            }
            _ => {
                // Taking address of non-lvalue reference
                self.add_error(CheckerError::CantTakeAddrOfRvalExpr(ampersand.clone()));
                None
            }
        }
    }

    /// Validates a let expression.
    fn pass_let_expr(
        &mut self,
        mutable: bool,
        loc_or_let: &Loc,
        name: &Identifier,
        ty: Option<&(Loc, Type)>,
        eq: &Loc,
        expr: &Expr,
    ) -> Option<(Type, HIRExpr)> {
        let (value_ty, value_hir) = self.pass_reachable_expr(
            expr,
            ExprState::IsExpr,
            None,
        )?;
        let actual_ty = ty.map(|t| &t.1).unwrap_or(&value_ty);
        let binding = Some(loc_or_let.clone());
        self.pass_slot_decl(
            name,
            actual_ty,
            if mutable {
                &binding
            } else {
                &None
            },
        )?;
        self.pass_assignment(
            &AssignmentExpr(BinaryExpr {
                left_hand_side: Box::new(
                    Expr::AsReference(
                        AsReferenceExpr(
                            name.0.clone(),
                            Box::new(
                                Expr::Variable(name.clone()),
                            )
                        )
                    )
                ),
                op: (eq.clone(), BinaryOp::Plus),
                right_hand_side: Either::Left(Box::new(expr.clone())),
            })
        )
    }

    /// Validates a literal expression.
    fn pass_lit_expr(&mut self, expr: &LiteralExpr, expected_type: Option<Type>) -> Option<(Type, HIRExpr)> {
        match expr {
            LiteralExpr::Int(_, i) => {
                // return an int type
                if let Some(Type::Primitive { loc, ty: PrimType::Int(bits) }) = expected_type {
                    let max_value = match bits {
                        TypeBits::B64 => i64::MAX as u64,
                        TypeBits::B32 => i32::MAX as u64,
                        TypeBits::B16 => i16::MAX as u64,
                        TypeBits::B8 => i8::MAX as u64,
                    };

                    if i.2 > max_value {
                        self.add_error(
                            CheckerError::LitTooBigForTy(
                                i.clone(),
                                Type::Primitive { loc, ty: PrimType::Int(bits) },
                                max_value
                            )
                        );
                        None
                    } else {
                        Some((
                            Type::Primitive { loc, ty: PrimType::Int(bits) },
                            HIRExpr::Literal(
                                HIRLiteralExpr::Int(
                                    self.pass_ty(Type::Primitive { loc, ty: PrimType::Int(bits) })?,
                                    i.clone(),
                                )
                            )
                        ))
                    }
                } else if let Some(Type::Primitive { loc, ty: PrimType::UInt(bits) }) = expected_type {
                    if i.1 {
                        // unsigned integer does not support negative numbers
                        self.add_error(
                            CheckerError::IntTyNonNeg(
                                i.clone(),
                                Type::Primitive { loc, ty: PrimType::UInt(bits) },
                            )
                        );
                        None
                    } else {
                        let max_value = match bits {
                            TypeBits::B64 => u64::MAX,
                            TypeBits::B32 => u32::MAX as u64,
                            TypeBits::B16 => u16::MAX as u64,
                            TypeBits::B8 => u8::MAX as u64,
                        };

                        if i.2 > max_value {
                            self.add_error(
                                CheckerError::LitTooBigForTy(
                                    i.clone(),
                                    Type::Primitive { loc, ty: PrimType::UInt(bits) },
                                    max_value
                                )
                            );
                            None
                        } else {
                            Some((
                                Type::Primitive { loc, ty: PrimType::UInt(bits) },
                                HIRExpr::Literal(
                                    HIRLiteralExpr::Int(
                                        self.pass_ty(Type::Primitive { loc, ty: PrimType::Int(bits) })?,
                                        i.clone(),
                                    )
                                )
                            ))
                        }
                    }
                } else {
                    Some((
                        Type::new_primitive(i.0.clone(), PrimType::new_int(TypeBits::B64)),
                        HIRExpr::Literal(
                            HIRLiteralExpr::Int(
                                self.pass_ty(Type::Primitive { loc: i.0.clone(), ty: PrimType::Int(TypeBits::B32) })?,
                                i.clone(),
                            )
                        )
                    ))
                }
            }
        }
    }

    /// Validastes the dereferencing of a pointer.
    fn pass_dereference_expr(&mut self, deref: &Loc, base: &Expr) -> Option<(Type, HIRExpr)> {
        let (base_ty, base_hir) = self.pass_reachable_expr(base, ExprState::IsExpr, None)?;

        if let Type::Pointer { pointee, mutability: _, lifetime: _ } = &base_ty {
            let hir_pointee = self.pass_ty(*pointee.clone())?;
            Some(((**pointee).clone(), HIRExpr::Dereference(hir_pointee, Box::new(base_hir))))
        } else {
            self.add_error(
                CheckerError::DerefNonPtrTy(deref.clone(), base_ty)
            );

            None
        }
    }

    /// Validates the instantiation of a struct.
    fn pass_instantiate_struct(
        &mut self,
        struct_name: &Identifier,
        expr_fields: &[(Identifier, Expr)],
    ) -> Option<(Type, HIRExpr)> {
        if let Some(Member::Type(ty)) = self.ctx.lookup_member(&struct_name.index()) {
            match &ty.borrow().ty {
                UserType::Struct(Struct { fields }) => {
                    let struct_ty = self.pass_ty(Type::NamedType(struct_name.clone()))?;

                    self.pass_instantiate_struct_impl(
                        struct_name,
                        struct_name,
                        struct_ty,
                        expr_fields,
                        fields
                    )
                }
                UserType::Union(fields) => {
                    let union_ty = self.pass_ty(Type::NamedType(struct_name.clone()))?;

                    if expr_fields.len() != 1 {
                        // can only specify one field at a time for an union
                        self.add_error(
                            CheckerError::UnionMultipleFieldInstantiation(struct_name.0.clone())
                        );
                        None
                    } else {
                        let (spec_field_name, spec_field_expr) = expr_fields.first().cloned().unwrap();
                        
                        for (field_name, field_ty) in fields.iter() {
                            if field_name == &spec_field_name {
                                let (spec_field_ty, spec_field_hir) = self.pass_reachable_expr(&spec_field_expr, ExprState::IsExpr, Some(field_ty.clone()))?;
                                if !self.types_are_same(spec_field_name.loc(), &field_ty, &spec_field_ty)? {
                                    self.add_error(CheckerError::WrongTyForField {
                                        struct_name: struct_name.clone(),
                                        field_name: field_name.clone(),
                                        supplied_ty: spec_field_ty,
                                        expected_ty: field_ty.clone(),
                                        instantiating: "union",
                                    });
                                    return None
                                } else {
                                    return Some((
                                        Type::NamedType(struct_name.clone()),
                                        HIRExpr::new_instantiate_union(
                                            union_ty,
                                            Box::new(spec_field_hir),
                                            self.type_is_aggregate(spec_field_ty),
                                        )
                                    ))
                                }
                            }
                        }

                        // no such field
                        self.add_error(
                            CheckerError::InvalidUnionField {
                                uni: struct_name.clone(),
                                field: spec_field_name,
                            }
                        );
                        None
                    }
                }
                _ => {

                    self.add_error(
                        CheckerError::InstantiatingNonStructType(struct_name.clone())
                    );

                    None
                }
            }
        } else {
            self.add_error(
                CheckerError::NamedTypeNotFound(struct_name.clone())
            );

            None
        }
    }

    fn pass_instantiate_struct_impl(
        &mut self,
        struct_name: &Identifier,
        debug_name: &Identifier,
        struct_ty: HIRType,
        expr_fields: &[(Identifier, Expr)],
        fields: &[(Identifier, Type)]
    ) -> Option<(Type, HIRExpr)> {
        if expr_fields.len() != fields.len() {
            self.add_error(CheckerError::WrongFieldNumberForStruct {
                name: debug_name.clone(),
                received: expr_fields.len(),
                needed: fields.len(),
            });

            None
        } else {
            // check for each field
            let mut hir_fields = Vec::new();

            for (_, field) in fields.iter().enumerate() {
                if let Some((spec_name, field_expr)) = expr_fields.iter().find(|(name, _)| name == &field.0) {
                    // number of expressions for field
                    let provided_exprs_for_field = expr_fields.iter().filter(|value| &value.0 == spec_name).count();
                    
                    // check if repeated
                    if provided_exprs_for_field != 1 {
                        self.add_error(CheckerError::RepeatedFieldInInstantiation {
                            field: field.0.clone(),
                            provided: provided_exprs_for_field,
                        });
                        
                        return None;
                    }
                    
                    // pass field expr
                    let (spec_field_ty, spec_field_hir) = self.pass_reachable_expr(field_expr, ExprState::IsExpr, Some(field.1.clone()))?;

                    if !self.types_are_same(spec_name.loc(), &spec_field_ty, &field.1)? {
                        self.add_error(CheckerError::WrongTyForField {
                            struct_name: debug_name.clone(),
                            field_name: field.0.clone(),
                            supplied_ty: spec_field_ty.clone(),
                            expected_ty: field.1.clone(),
                            instantiating: "struct",
                        })
                    }
                    
                    hir_fields.push((spec_field_hir, self.type_is_aggregate(spec_field_ty)));
                } else {
                    self.add_error(CheckerError::FieldNotProvidedWhenInstantiating {
                        struct_name: debug_name.clone(),
                        field: field.0.clone(),
                        ty: field.1.clone(),
                    });

                    return None
                }
            }

            // implement here

            Some((
                Type::new_named_type(struct_name.clone()),
                HIRExpr::new_instantiate_struct(
                    struct_ty,
                    hir_fields,
                )
            ))
        }
    }

    fn pass_instantiate_struct_impl_hir(
        &mut self,
        struct_name: &Identifier,
        struct_ty: HIRType,
        hir_fields: Vec<(HIRExpr, Option<HIRType>)>,
    ) -> Option<(Type, HIRExpr)> {
        Some((
            Type::new_named_type(struct_name.clone()),
            HIRExpr::new_instantiate_struct(
                struct_ty,
                hir_fields,
            )
        ))
    }

    /// Validates a binary expression.
    fn pass_bin_expr(
        &mut self,
        BinaryExpr {
            left_hand_side,
            op,
            right_hand_side,
        }: &BinaryExpr,
    ) -> Option<(Type, HIRExpr)> {
        let (lhs_ty, lhs_hir) = self.pass_reachable_expr(&left_hand_side, ExprState::IsExpr, None)?;
        let (rhs_ty, rhs_hir) = match right_hand_side {
            Either::Left(rhs) => self.pass_reachable_expr(&rhs, ExprState::IsExpr, None)?,
            Either::Right((rhs_ty, rhs_hir)) => (rhs_ty.clone(), rhs_hir.clone()),
        };

        if !self.types_are_same(&left_hand_side.loc(), &lhs_ty, &rhs_ty)? {
            // cannot use binary operator in different types
            self.add_error(CheckerError::BinOnDiffTys(
                left_hand_side.loc(),
                lhs_ty,
                rhs_ty,
            ));
            None
        } else {
            self.check_if_supports_operator(left_hand_side.loc(), &lhs_ty, &op.1)?;
            let op_ty = binary_operation_type_of(&lhs_ty);
            Some((
                lhs_ty,
                HIRExpr::Binary(HIRBinaryExpr {
                    left_hand_side: Box::new(lhs_hir),
                    op: op.clone(),
                    right_hand_side: Box::new(rhs_hir),
                    op_ty,
                }),
            ))
        }
    }

    /// Validates the access of an expression.
    fn pass_access_property(
        &mut self,
        base: &Expr,
        dot: Loc,
        prop: &Identifier,
    ) -> Option<(Type, HIRExpr, Option<usize>)> {
        // check if this is sum type instantiation as in Result.Ok without arguments
        if let Expr::Variable(possible_sum_ty) = base {
            if let Some(Member::Type(user_ty)) = self.ctx.lookup_member(&possible_sum_ty.1) {
                let borrowed = user_ty.borrow();
                if let CtxUserType { ty: UserType::Sum(variants), .. } = &*borrowed {
                    return self.pass_instantiate_sum(possible_sum_ty, prop, None, variants)
                        .map(|value| (value.0, value.1, None))
                }
            }
        }

        let (base_ty, base_val) = self.pass_reachable_expr(base, ExprState::IsExpr, None)?;

        let hir_ty = self.pass_ty(base_ty.clone())?;
        let mut life_time = None;

        if let Expr::Variable(v) = base {
            let (_, _, _, _, lifetime) = self.get_var(&base.loc(), &v.1, false, false)?;
            life_time = Some(lifetime);
        }

        // check if we are accessing Struct or *Struct
        let (name, requires_dereferencing, hir_ty) = match &base_ty {
            Type::Pointer { pointee, mutability: _, lifetime } => {
                life_time = *lifetime;
                if let Type::NamedType(name) = &**pointee {
                    (name, true, if let HIRType::Pointer { pointee, .. } = hir_ty {
                        *pointee
                    } else {
                        unreachable!()
                    })
                } else {
                    self.add_error(
                        CheckerError::AccPropOfNonAggrTy(dot, base_ty)
                    );
                    return None
                }
            }
            Type::NamedType(name) => (name, false, hir_ty),
            _ => {
                self.add_error(
                    CheckerError::AccPropOfNonAggrTy(dot, base_ty)
                );
                return None
            }
        };
        if let Some(Member::Type(actt)) = self.ctx.lookup_member(&name.index()) {
            if let CtxUserType { ty: UserType::Struct(Struct { fields }), .. } = &*actt.borrow() {

                if let Some((field_index, (_, field_type))) = fields.iter().enumerate().find(|element| element.1.0.index() == prop.index()) {
                    let expr = HIRExpr::new_access_struct_property(
                        Box::new(base_val),
                        hir_ty,
                        field_index as u32,
                        self.pass_ty(field_type.clone())?,
                        requires_dereferencing,
                    );
                    
                    Some((field_type.clone(), expr, life_time))
                } else {
                    self.add_error(
                        CheckerError::NoSuchPropAtStruct(base_ty, prop.clone())
                    );
                    None
                }
                
            } else if let CtxUserType { ty: UserType::Union(fields), .. } = &*actt.borrow() {

                if let Some((field_index, (_, field_type))) = fields.iter().enumerate().find(|element| element.1.0.index() == prop.index()) {
                    let expr = HIRExpr::new_access_union_property(
                        Box::new(base_val),
                        self.pass_ty(field_type.clone())?,
                        requires_dereferencing,
                    );
                    
                    Some((field_type.clone(), expr, life_time))
                } else {
                    self.add_error(
                        CheckerError::NoSuchPropAtStruct(base_ty, prop.clone())
                    );
                    None
                }
                
            } else {
                self.add_error(
                    CheckerError::AccPropOfNonAggrTy(dot, base_ty)
                );
                None
            }
        } else {
            self.add_error(
                CheckerError::AccPropOfNonAggrTy(dot, base_ty)
            );
            None
        }
    }

    /// Validates the calling of a method.
    /// 
    /// It can also be the instantiation of a sum variant.
    fn pass_method_call(&mut self, base: &Expr, method_name: &Identifier, params: &[Expr]) -> Option<(Type, HIRExpr)> {
        // check if this is sum type instantiation as in Result.Ok(...args)
        if let Expr::Variable(possible_sum_ty) = base {
            if let Some(Member::Type(user_ty)) = self.ctx.lookup_member(&possible_sum_ty.1) {
                let borrowed = user_ty.borrow();
                if let CtxUserType { ty: UserType::Sum(variants), .. } = &*borrowed {
                    return self.pass_instantiate_sum(possible_sum_ty, method_name, Some(params), variants)
                }
            }
        }

        // get the type and HIR for base
        let (base_ty, base_hir) = self.pass_reachable_expr(base, ExprState::IsExpr, None)?;
        
        let mut params_hir = vec![];
        for param in params {
            params_hir.push(
                self.pass_reachable_expr(param, ExprState::IsExpr, None)?
            );
        }

        // check if it is a named type
        if let Type::NamedType(name) = &base_ty {
            // check if this type actually exists
            if let Some(Member::Type(user_type)) = self.ctx.lookup_member(&name.index()) {
                // check if method exists
                let binding = user_type.borrow();
                if let Some(method) = binding.methods.get(&method_name.index()) {
                    // get its name
                    let method_binding = method.borrow();
                    let proto = method_binding.proto.clone();
                    let name_of_function = method_binding.full_name(&self.collection);
                    drop(method_binding);

                    let proto_of_function = self.pass_proto(&proto, method)?;
                    // check if it actually takes it by value
                    let base_hir = if &base_ty == &**proto.receiver.as_ref().unwrap().ty() {
                        base_hir
                    } else {
                        // if it's supposed to take by reference append `HIRAsReferenceExpr` to the base
                        HIRExpr::AsReference(
                            HIRAsReferenceExpr(
                                base.loc(),
                                Box::new(
                                    base_hir
                                )
                            )
                        )
                    };

                    if params_hir.len() != proto.arguments.len() {
                        self.add_error(CheckerError::FuncGotDiffParamSizeThanInProto {
                            call_at: method_name.loc().clone(),
                            in_proto: proto.arguments().len(),
                            received: params.len(),
                            type_of_func_is: Type::FunctionPointer(proto.clone()),
                        });
                        return None;
                    }

                    let mut actual_params = vec![base_hir];

                    for ((ty, hir), arg) in params_hir.into_iter().zip(proto.arguments.iter()) {
                        if !self.types_are_same(method_name.loc(), &ty, &arg.ty)? {
                            self.add_error(
                                CheckerError::WrongParamTy {
                                    param: arg.name.index(),
                                    expected: arg.ty.clone(),
                                    received: ty.clone(),
                                    expr_loc: method_name.0.clone(),
                                }
                            );
                        }
                        actual_params.push(hir);
                    }

                    Some((
                        (**proto.return_type()).clone(),
                        HIRExpr::new_call(
                            HIRCallExpr::new(
                                Box::new(HIRExpr::new_global_func(
                                    name_of_function,
                                    proto_of_function
                                )),
                                actual_params,
                                self.type_is_aggregate((**proto.return_type()).clone()),
                            )
                        )
                    ))
                } else {

                    self.add_error(
                        CheckerError::MethodNotFoundForAggr {
                            aggr: name.clone(),
                            method: method_name.clone(),
                        }
                    );
                    None
                }
            } else {
                self.add_error(
                    CheckerError::NamedTypeNotFound(name.clone())
                );
                None
            }
        } else if let Type::Pointer { pointee, mutability, lifetime } = &base_ty {
            if let Type::NamedType(name) = &**pointee {
                // call on method which takes by-reference
                // check if this type actually exists
                if let Some(Member::Type(user_type)) = self.ctx.lookup_member(&name.index()) {
                    // check if method exists
                    let binding = user_type.borrow();
                    if let Some(method) = binding.methods.get(&method_name.index()) {
                        // get its name
                        let method_binding = method.borrow();
                        let proto = method_binding.proto.clone();
                        let name_of_function = method_binding.full_name(&self.collection);
                        drop(method_binding);

                        let proto_of_function = self.pass_proto(&proto, method)?;
                        // check if it actually takes it by value
                        let base_hir = if &base_ty == &**proto.receiver.as_ref().unwrap().ty() {
                            base_hir
                        } else {
                            // if it's supposed to take by reference append `HIRAsReferenceExpr` to the base
                            self.add_error(
                                CheckerError::CallMethodWhichTakesByValueRecOnPtr {
                                    aggr: name.clone(),
                                    method: method_name.clone(),
                                }
                            );
                            return None;
                        };

                        if params_hir.len() != proto.arguments.len() {
                            self.add_error(CheckerError::FuncGotDiffParamSizeThanInProto {
                                call_at: method_name.loc().clone(),
                                in_proto: proto.arguments().len(),
                                received: params.len(),
                                type_of_func_is: Type::FunctionPointer(proto.clone()),
                            });
                            return None;
                        }

                        let mut actual_params = vec![base_hir];

                        for ((ty, hir), arg) in params_hir.into_iter().zip(proto.arguments.iter()) {
                            if !self.types_are_same(method_name.loc(), &ty, &arg.ty)? {
                                self.add_error(
                                    CheckerError::WrongParamTy {
                                        param: arg.name.index(),
                                        expected: arg.ty.clone(),
                                        received: ty.clone(),
                                        expr_loc: method_name.0.clone(),
                                    }
                                );
                            }
                            actual_params.push(hir);
                        }

                        Some((
                            (**proto.return_type()).clone(),
                            HIRExpr::new_call(
                                HIRCallExpr::new(
                                    Box::new(HIRExpr::new_global_func(
                                        name_of_function,
                                        proto_of_function
                                    )),
                                    actual_params,
                                    self.type_is_aggregate((**proto.return_type()).clone()),
                                )
                            )
                        ))
                    } else {

                        self.add_error(
                            CheckerError::MethodNotFoundForAggr {
                                aggr: name.clone(),
                                method: method_name.clone(),
                            }
                        );
                        None
                    }
                } else {
                    self.add_error(
                        CheckerError::NamedTypeNotFound(name.clone())
                    );
                    None
                }
            } else {
                // TODO: Calling methods on primitive types
                todo!("Calling methods on primitive types")
            }
        } else {
            // TODO: Calling methods on primitive types
            todo!("Calling methods on primitive types")
        }
    }

    /// Passes through the instantiation of a sum type.
    fn pass_instantiate_sum(
        &mut self,
        sum_name: &Identifier,
        variant_name: &Identifier,
        params: Option<&[Expr]>,
        variants: &[SumVariant]
    ) -> Option<(Type, HIRExpr)> {
        let mut variant_fields = vec![];
        for variant in variants {
            if let Some(sum_fields) = &variant.aggregate_fields {
                let mut new_fields = vec![];
                for (field, ty) in sum_fields.fields().iter() {
                    new_fields.push((field.clone(), ty.clone()));
                }
                variant_fields.push(self.struct_hir_ty_from_fields(
                    &new_fields
                )?);
            }
        }

        // get the hir type of the sum
        let mut sum_fields = vec![HIRType::Primitive {
            loc: Loc::default(),
            ty: PrimType::UInt(TypeBits::B64),
        }];
        let mut actual_fields = vec![];
        if !variant_fields.is_empty() {
            actual_fields.push(HIRType::Union(variant_fields));
        }
        sum_fields.extend(actual_fields.clone().into_iter());
        let sum_type_hir = self.struct_hir_ty_from_hir_fields(
            &sum_fields
        )?;

        for variant in variants {
            // check if the name is equal
            if variant.name() == variant_name {
                // get its d
                let discriminant = variant.discriminant.2;
                let (_, discriminant_hir) = self.pass_lit_expr(
                    &LiteralExpr::Int(
                        Type::new_primitive(
                            Loc::default(),
                            PrimType::Int(TypeBits::B64),
                        ),
                        IntLit(Loc::default(), false, discriminant)
                    ),
                    Some(Type::new_primitive(
                        Loc::default(),
                        PrimType::Int(TypeBits::B64),
                    ))
                )?;
                // get everything correctly
                if variant.aggregate_fields.is_none() && params.is_some() {
                    self.add_error(
                        CheckerError::VariantDoesntTakeFields {
                            sum: sum_name.clone(),
                            variant: variant_name.clone(),
                        }
                    );
                    return None;
                } else if variant.aggregate_fields.is_some() && params.is_none() {
                    self.add_error(
                        CheckerError::VariantTakeFieldsButNotFound {
                            sum: sum_name.clone(),
                            variant: variant_name.clone(),
                        }
                    );
                    return None;
                } else {
                    // typecheck the fields if any
                    return match (params, variant.aggregate_fields()) {
                        (Some(params), Some(fields)) => {
                            let fields_struct_ty = self.struct_hir_ty_from_hir_fields(
                                &actual_fields
                            )?;
                            let sum_struct_ty = self.struct_hir_ty_from_hir_fields(
                                &sum_fields
                            )?;

                            let mut new_fields = vec![];
                            for (field, expr) in fields.fields().iter().zip(params.iter()) {
                                new_fields.push((field.0.clone(), expr.clone()));
                            }
                            let (_sum_fields_ty, sum_fields_hir) = self.pass_instantiate_struct_impl(
                                sum_name,
                                variant_name,
                                fields_struct_ty,
                                &new_fields,
                                &fields.fields()
                            )?;
                            self.pass_instantiate_struct_impl_hir(
                                sum_name,
                                sum_struct_ty.clone(),
                                vec![
                                    (discriminant_hir, None),
                                    (sum_fields_hir, Some(sum_struct_ty)),
                                ]
                            )
                        }
                        _ => {
                            Some((
                                Type::NamedType(sum_name.clone()),
                                HIRExpr::new_instantiate_struct(
                                    sum_type_hir,
                                    vec![(discriminant_hir, None)]
                                )
                            ))
                        }
                    }
                }
            }
        }

        // sum variant not found within
        self.add_error(
            CheckerError::NoSuchSumVariant {
                sum: sum_name.clone(),
                variant: variant_name.clone(),
            }
        );

        None
    }

    /// Validates the instantiation of a generic.
    fn pass_generic_instantiation(&mut self, name: &Identifier, templates: &[Type]) -> Option<(
        Type, HIRExpr
    )> {
        if let Some(Member::GenericFunction(func)) = self.ctx.lookup_member(&name.index()) {
            // checks for generic instantiation
            self.instantiate_generic_with(
                name.clone(),
                templates,
                &func,
            )
        } else {
            self.add_error(
                CheckerError::GenericFunctionNotFound(name.clone()),
            );
            None
        }
    }

    /// Instantiates a generic function.
    fn instantiate_generic_with(&mut self, name: Identifier, templates: &[Type], function: &ActGenericFunction) -> Option<(Type, HIRExpr)> {
        let func = function.borrow();
        let generics_ = func.decl().prototype.generics().as_ref().unwrap();
        let generics = generics_.generics();

        if generics.len() != templates.len() {
            self.add_error(
                CheckerError::InvalidTemplParamLen {
                    name,
                    expected: generics.len(),
                    found: templates.len(),
                }
            );

            None
        } else {
            if let Some((_, _function_found, hir_prototype, prototype)) = func.instantiated.iter().find(|generic| generic.0.as_slice() == templates) {
                // return if we already instantiated with these template
                // arguments
                return Some((
                    Type::new_function_pointer(prototype.clone()),
                    HIRExpr::GlobalFunc(
                        hir_prototype.name.clone(),
                        hir_prototype.clone(),
                    )
                ))
            }

            // define this function
            let namespace_of_definition = func.parent
                .upgrade()
                .unwrap();

            let new_name = format!("{}<{}>", func.full_name(self.collection()), templates.iter().map(|v| ty_to_string(v, self.collection())).collect::<Vec<_>>().join(", "));
            let new_name_tag = self.collection.add(new_name);
            let new_name_id = Identifier(name.loc().clone(), new_name_tag);

            let mut decl = func.decl.clone();

            let mut generics_to_replace = HashMap::new();

            for (Generic { name }, generic_ty) in generics.iter().zip(templates.iter()) {
                generics_to_replace.insert(
                    name.index(),
                    generic_ty.clone()
                );
            }

            // replace generics internally
            decl.replace_generic(new_name_id, &generics_to_replace);

            let new_proto = decl.prototype.clone();

            // restart the namespace and define it
            self.ctx.start_specified_namespace(namespace_of_definition);

            let hir_decl = self.pass_function_decl(&decl)?;
            let (defined_name, hir_prototype) = if let HIRDecl::FunctionDecl(decl) = &hir_decl {
               (decl.prototype.name.clone(), decl.prototype.clone())
            } else {
                unreachable!()
            };

            self.ctx.end_namespace();

            Some((
                Type::new_function_pointer(new_proto),
                HIRExpr::DefineAndEval(hir_decl, Box::new(HIRExpr::GlobalFunc(
                    defined_name,
                    hir_prototype,
                )))
            ))
        }
    }

    /// Validates the call a function.
    fn pass_call_expr(
        &mut self,
        CallExpr { callee, params }: &CallExpr,
    ) -> Option<(Type, HIRExpr)> {
        // get type of callee
        let (callee_type, callee_hir) = self.pass_reachable_expr(&callee, ExprState::IsExpr, None)?;

        if let Type::FunctionPointer(ref prototype) = callee_type {
            // validate parameters

            let mut hir_params = vec![];

            /*
            check for difference in expected param size
            and in received param size
            */
            if prototype.arguments().len() != params.len() {
                self.add_error(CheckerError::FuncGotDiffParamSizeThanInProto {
                    call_at: callee.loc(),
                    in_proto: prototype.arguments().len(),
                    received: params.len(),
                    type_of_func_is: callee_type.clone(),
                })
            } else {
                // check types of each statement

                // if there are generics
                if prototype.generics().is_none() {
                    // there aren't any generics
                    for (arg, param) in prototype.arguments().iter().zip(params.iter()) {
                        let (param_ty, param_expr) =
                            self.pass_reachable_expr(param, ExprState::IsExpr, None)?;
    
                        if !self.types_are_same(&param.loc(), &param_ty, &arg.ty)? {
                            self.add_error(CheckerError::WrongParamTy {
                                param: arg.name.index(),
                                expected: arg.ty.clone(),
                                received: param_ty,
                                expr_loc: param.loc(),
                            });
                        }
    
                        hir_params.push(param_expr);
                    }
                }
            }

            // return proto return type here
            Some((
                (**prototype.return_type()).clone(),
                HIRExpr::Call(HIRCallExpr {
                    callee: Box::new(callee_hir),
                    params: hir_params,
                    returns_aggregate: self.type_is_aggregate((**prototype.return_type()).clone()),
                }),
            ))
        } else {
            // calling non function type
            self.add_error(CheckerError::CallNonFunc(callee.loc(), callee_type));

            None
        }
    }

    /// Validates an assignment.
    fn pass_assignment(
        &mut self,
        AssignmentExpr(BinaryExpr {
            left_hand_side,
            op,
            right_hand_side,
        }): &AssignmentExpr,
    ) -> Option<(Type, HIRExpr)> {
        let (variable, variable_hir_expr) =
            self.pass_reachable_expr(&left_hand_side, ExprState::IsAssignmentLhs, None)?;

        if let Type::Pointer { pointee, mutability: Some(mutability), lifetime } = variable {
            let (type_of_expression, expression_hir) =
                self.pass_reachable_expr((right_hand_side.as_ref()).unwrap_left(), ExprState::IsExpr, Some((*pointee).clone()))?;

            // if we're assigning a pointer and we know its lifetime
            if let Type::Pointer { pointee: val_pointee, mutability: val_mut, lifetime: Some(lifetime_of_pointer) } = type_of_expression.clone() {
                // if the lifetime of the variable is greater than the
                // lifetime of the pointer
                if lifetime.unwrap() > lifetime_of_pointer {
                    self.add_error(
                        CheckerError::LifetimeOfVariableGreaterThanOfPointer(
                            (right_hand_side.as_ref()).unwrap_left().loc(),
                            Type::Pointer { pointee: pointee.clone(), mutability: Some(mutability), lifetime },
                            Type::Pointer { pointee: val_pointee, mutability: val_mut, lifetime: Some(lifetime_of_pointer) }
                        )
                    );
                }
            }

            if !self.types_are_same(&op.0, &pointee, &type_of_expression)? {
                // assigning wrong type
                self.add_error(CheckerError::AssignWrongTy {
                    slot_ty: *pointee,
                    expr_loc: (right_hand_side.as_ref()).unwrap_left().loc(),
                    expr_ty: type_of_expression,
                });

                None
            } else {
                Some((
                    Type::new_universe(),
                    HIRExpr::Assignment(HIRAssignmentExpr(HIRBinaryExpr {
                        left_hand_side: Box::new(variable_hir_expr),
                        op: op.clone(),
                        right_hand_side: Box::new(expression_hir),
                        op_ty: BinOpType::Int,
                    }, self.type_is_aggregate(*pointee))),
                ))
            }
        } else if let Type::Pointer { pointee: _, mutability: None, lifetime: _ } = &variable {
            self.add_error(CheckerError::ChangeConst {
                lvalue_ty: variable,
                loc: left_hand_side.loc(),
            });
            None
        } else {
            // variable is always going to be an lvalue
            // so no need to check this
            unreachable!(
                "error in parser: left hand side of assignment is not an lvalue: is {variable:?}"
            )
        }
    }

    /// Typechecks a switch statement.
    fn pass_switch(&mut self, switch: &Switch) -> Option<(Type, Reachability, HIRExpr)> {
        // pass the expression
        let (type_of_value_switched_on, value_switched_on_hir) = self.pass_reachable_expr(switch.value(), ExprState::IsExpr, None)?;

        let mut pattern_is_currently_unreachable = false;
        let mut statement_reachability = Reachability::Unreachable;
        let mut hir_cases = vec![];

        for case in switch.patterns() {
            if pattern_is_currently_unreachable {
                self.add_error(
                    CheckerError::UnreachableCasePattern(
                        case.case().clone(),
                    )
                );
                break;
            }

            let result = self.pass_case(case, &type_of_value_switched_on)?;
            statement_reachability &= result.block_is_reachable;
            if !result.pattern_is_reachable {
                pattern_is_currently_unreachable = true;
            }
            hir_cases.push(result.case);
        }

        if !pattern_is_currently_unreachable {
            // cases were not matched
            self.add_error(
                CheckerError::NotAllPatsMatchedForTy(switch.switch_tok().clone(), type_of_value_switched_on)
            );
        }

        Some((
            Type::Void,
            statement_reachability,
            HIRExpr::new_switch(
                HIRSwitch::new(
                    Box::new(value_switched_on_hir),
                    hir_cases,
                )
            )
        ))
    }

    /// Typechecks a case statement.
    /// 
    /// Returns the HIR expression of the case statement and
    /// if it is reachable or not.
    fn pass_case(&mut self, case: &Case, value_ty: &Type) -> Option<CaseResult> {
        // get attributes from the case
        let pattern = case.pattern();
        let block = case.block();

        // pass through the pattern
        let (
            pattern_hir,
            is_reachable,
            names
        ) = self.pass_pattern(case.case(), pattern, value_ty)?;
        
        // set up the case block's scope
        self.ctx.add_normal_scope(false);
        // set up the bindings' names
        for (binding_name, binding_ty, binding_mutability) in names.into_iter() {
            self.ctx.insert_variable_in_last_scope(
                binding_name.index(),
                binding_ty,
                None,
                binding_mutability,
                true
            );
        }

        let (reachability, hir_block) = self.pass_block(block, false)?;

        // pop scope
        self.ctx.pop_scope();

        Some(CaseResult {
            case: HIRCase::new(pattern_hir, hir_block),
            pattern_is_reachable: is_reachable,
            block_is_reachable: reachability,
        })
    }

    /// Typechecks a single pattern.
    ///
    /// Returns the HIR expression of the pattern and if it is
    /// reachable or not.
    /// 
    /// Also returns the matched identifiers and their types.
    fn pass_pattern(&mut self, loc: &Loc, pattern: &Pattern, value_ty: &Type) -> Option<(HIRPattern, bool, Vec<(Identifier, Type, Mutability)>)> {
        use Pattern as P;

        match pattern {
            P::Literal(lit) => {
                // check if the literal used is valid
                let (literal_ty, literal_hir) = self.pass_reachable_expr(
                    &Expr::Literal(lit.clone()),
                    ExprState::IsExpr,
                    Some(value_ty.clone()),
                )?;
                if !self.types_are_same(
                    loc,
                    value_ty,
                    &literal_ty
                )? {
                    self.add_error(
                        CheckerError::InvalidPatForTy {
                            loc: loc.clone(),
                            switched_on: value_ty.clone(),
                            pattern_ty: literal_ty,
                        }
                    );
                    return None;
                }

                // literal patterns are always reachable
                Some((
                    HIRPattern::new_literal(self.pass_ty(literal_ty)?, if let HIRExpr::Literal(l) = literal_hir {
                        l
                    } else {
                        unreachable!()
                    }),
                    true,
                    vec![],
                ))
            }
            P::ExclusiveRange { begin, range_tok, end } => {
                self.pass_range(
                    loc,
                    begin,
                    range_tok,
                    end,
                    value_ty,
                    |this, left, right, range, value_type| {
                        // range exclusive for ints
                        let equivalent_left: i128 = left.clone().into();
                        let equivalent_right: i128 = right.clone().into();
                        // check if the range is invalid
                        if equivalent_right > equivalent_left {
                            this.add_error(
                                CheckerError::LeftGreaterThanRightInRange(
                                    range.clone(),
                                )
                            );
                        } else if equivalent_left == equivalent_right {
                            this.add_error(
                                CheckerError::RangeExclusiveWithEqualEnds(
                                    range.clone(),
                                )
                            );
                        }
                        
                        // exclusive range patterns are always reachable
                        Some((
                            HIRPattern::new_range(
                                this.pass_ty(value_type.clone())?,
                                HIRLiteralExpr::Int(
                                    this.pass_ty(value_type.clone())?,
                                    left.clone(),
                                ),
                                HIRLiteralExpr::Int(
                                    this.pass_ty(value_type.clone())?,
                                    IntLit(right.0.clone(), right.1, right.2 - 1),
                                )
                            ),
                            true,
                            vec![],
                        ))
                    }
                )
            }
            P::InclusiveRange { begin, range_tok, end } => {
                self.pass_range(
                    loc,
                    begin,
                    range_tok,
                    end,
                    value_ty,
                    |this, left, right, range, value_type| {
                        // range exclusive for ints
                        let equivalent_left: i128 = left.clone().into();
                        let equivalent_right: i128 = right.clone().into();
                        // check if the range is invalid
                        if equivalent_right > equivalent_left {
                            this.add_error(
                                CheckerError::LeftGreaterThanRightInRange(
                                    range.clone(),
                                )
                            );
                        }
                        // here we removed the check for equality because range inclusive
                        // allows for left == right
                        
                        // exclusive range patterns are always reachable
                        Some((
                            HIRPattern::new_range(
                                this.pass_ty(value_type.clone())?,
                                HIRLiteralExpr::Int(
                                    this.pass_ty(value_type.clone())?,
                                    left.clone(),
                                ),
                                HIRLiteralExpr::Int(
                                    this.pass_ty(value_type.clone())?,
                                    right.clone(),
                                )
                            ),
                            true,
                            vec![],
                        ))
                    }
                )
            }
            P::DeStructure { name, lkey_tok, fields, ignore, rkey_tok } => {
                self.pass_destructure(name, lkey_tok, fields.as_slice(), ignore.as_ref(), rkey_tok, value_ty)
            }
            P::WildCard(mutability, name) => {
                let value_hir_ty = self.pass_ty(value_ty.clone())?;
                let is_aggr = value_hir_ty.is_aggr();
                Some((
                    HIRPattern::new_wild_card(
                        value_hir_ty,
                        is_aggr,
                        self.collection().unwrap_get(name.index()).to_owned(),
                    ),
                    false,
                    vec![
                        (name.clone(), value_ty.clone(), mutability.clone())
                    ]
                ))
            }
        }
    }

    /// Passes through a range.
    /// 
    /// Takes in the `case` token and the `..` (range)
    /// token for debugging information, the value of
    /// the type being matched on, the begin and end
    /// values of the range and handlers for all of
    /// the values.
    fn pass_range(
        &mut self,
        case_tok: &Loc,
        begin: &LiteralExpr,
        range_tok: &Loc,
        end: &LiteralExpr,
        value_ty: &Type,
        int_handler: fn(this: &mut Self, &IntLit, &IntLit, &Loc, &Type) -> Option<(HIRPattern, bool, Vec<(Identifier, Type, Mutability)>)>,
    ) -> Option<(HIRPattern, bool, Vec<(Identifier, Type, Mutability)>)> {
        // check if range has same types
        let (begin_ty, _begin_hir) = self.pass_reachable_expr(
            &Expr::Literal(begin.clone()),
            ExprState::IsExpr,
            Some(value_ty.clone()),
        )?;
        let (end_ty, _end_hir) = self.pass_reachable_expr(
            &Expr::Literal(end.clone()),
            ExprState::IsExpr,
            Some(value_ty.clone()),
        )?;
        if !self.types_are_same(
            case_tok,
            &begin_ty,
            &end_ty,
        )? {
            self.add_error(
                CheckerError::RangeEndsTyDiff {
                    begin_ty: begin_ty.clone(),
                    range: range_tok.clone(),
                    end_ty,
                }
            );
        }
        // check if types support ranging
        if let (LiteralExpr::Int(_, i1), LiteralExpr::Int(_, i2)) = (begin, end) {
            int_handler(self, i1, i2, range_tok, value_ty)
        } else {
            self.add_error(
                CheckerError::LitDoesntSupportRange(range_tok.clone(), begin_ty)
            );
            None
        }
    }

    /// Typechecks the destructuring of a struct.
    fn pass_destructure(
        &mut self,
        name: &Identifier,
        lkey_tok: &Loc,
        fields: &[(Mutability, Identifier, Option<Pattern>)],
        ignore: Option<&Loc>,
        rkey_tok: &Loc,
        value_ty: &Type,
    ) -> Option<(HIRPattern, bool, Vec<(Identifier, Type, Mutability)>)> {
        if !self.types_are_same(name.loc(), value_ty, &Type::NamedType(name.clone()))? {
            self.add_error(CheckerError::InvalidPatForTy {
                loc: name.loc().clone(),
                switched_on: value_ty.clone(),
                pattern_ty: Type::NamedType(name.clone()),
            })
        }
        let mut names = vec![];
        let (pattern, reachable) = self.pass_destructure_impl(
            name,
            lkey_tok,
            fields,
            ignore,
            rkey_tok,
            &mut names
        )?;
        Some((pattern, reachable, names))
    }
    
    /// Typechecks the destructuring of a struct.
    fn pass_destructure_impl(
        &mut self,
        name: &Identifier,
        lkey_tok: &Loc,
        fields: &[(Mutability, Identifier, Option<Pattern>)],
        ignore: Option<&Loc>,
        rkey_tok: &Loc,
        names: &mut Vec<(Identifier, Type, Mutability)>,
    ) -> Option<(HIRPattern, bool)> {
        use Pattern as P;

        // get the aggregate type
        if let Some(Member::Type(aggr_ty)) = self.ctx.lookup_member(&name.index()) {
            // if it's an union, we can only match one field at a time
            // if it's a struct, then we don't need so
            let binding = aggr_ty.borrow();
            let CtxUserType { ty, parent: _, methods: _ } = &*binding;
            match ty {
                UserType::Struct(struct_ty) => {
                    self.handle_struct_destructure(name, struct_ty, fields, ignore, names)
                }
                UserType::Union(union_ty) => {
                    // error if nothing is provided
                    if fields.len() == 0 && ignore.is_none() {
                        self.add_error(
                            CheckerError::NoFieldsSpecifiedToUnionPattern {
                                name: name.clone(),
                            },
                        );
                    }
                    // error if anything more than one is provided
                    else if fields.len() != 1 {
                        self.add_error(
                            CheckerError::TooManyFieldsSpecifiedForUnionPattern {
                                name: name.clone(),
                                amount: fields.len(),
                            },
                        );
                    }

                    self.handle_union_destructure(name, &union_ty, fields.first().unwrap(), names)
                }
                UserType::Sum(_) => {
                    self.add_error(
                        CheckerError::MustSpecifyVariantDestructSumTy(name.clone()),
                    );
                    None
                }
                UserType::Alias(_) => {
                    self.add_error(
                        CheckerError::MatchingOnAlias(name.clone()),
                    );
                    None
                }
            }
        } else {
            self.add_error(
                CheckerError::NamedTypeNotFound(name.clone()),
            );
            None
        }
    }

    /// Handles the destructuring of structs.
    fn handle_struct_destructure(
        &mut self,
        name: &Identifier,
        struct_ty: &Struct,
        fields: &[(Mutability, Identifier, Option<Pattern>)],
        ignore: Option<&Loc>,
        names: &mut Vec<(Identifier, Type, Mutability)>,
    ) -> Option<(HIRPattern, bool)> {
        // error if too much fields are specified
        if fields.len() > struct_ty.fields.len() {
            self.add_error(
                CheckerError::TooManyStructFieldsMatchedInPat {
                    name: name.clone(),
                    expected: struct_ty.fields.len(),
                    found: fields.len()
                }
            );
        }
        // error if all fields are not handled
        else if fields.len() != struct_ty.fields.len() && ignore.is_none() {
            self.add_error(
                CheckerError::StructFieldsNotMatchedInPat {
                    name: name.clone(),
                    expected: struct_ty.fields.len(),
                    found: fields.len()
                }
            );
        }
        // check for the fields if this is always reachable or not
        let mut is_reachable = false;
        // the new constructed fields
        let mut new_fields: Vec<(String, usize, HIRPattern, HIRType)> = Vec::new();
        // go through fields
        for (field_mutability, field_name, pattern) in fields.iter() {
            // check if field doesn't exist
            if let Some((index, (_, field_ty))) = struct_ty.fields.iter().enumerate().find(|field| &field.1.0 == field_name) {
                // handle pattern for field
                let (field_hir, _) = self.handle_aggregate_field_pattern(
                    pattern.as_ref(),
                    field_mutability,
                    field_name,
                    &mut is_reachable,
                    field_ty,
                    names
                )?;
                // add to hir fields
                new_fields.push((
                    self.name(field_name),
                    index,
                    field_hir,
                    self.pass_ty(field_ty.clone())?,
                ));
            } else {
                // property doesn't exist at struct
                self.add_error(
                    CheckerError::NoSuchPropAtStruct(
                        Type::new_named_type(name.clone()),
                        field_name.clone(),
                    )
                );
            }
        }

        
        Some((
            HIRPattern::new_de_structure(
                self.pass_ty(Type::new_named_type(name.clone()))?,
                false,
                new_fields,
            ),
            is_reachable
        ))
    }

    /// Handles typechecking of a single pattern
    /// of a field of an aggregate type
    fn handle_aggregate_field_pattern(
        &mut self,
        pattern: Option<&Pattern>,
        field_mutability: &Mutability,
        field_name: &Identifier,
        is_reachable: &mut bool,
        field_ty: &Type,
        names: &mut Vec<(Identifier, Type, Mutability)>,
    ) -> Option<(HIRPattern, bool)> {
        use Pattern as P;

        match pattern {
            Some(P::WildCard(mutability, name)) => {
                // add name to names
                names.push((
                    name.clone(),
                    field_ty.clone(),
                    mutability.clone(),
                ));

                let is_aggr = self.type_is_aggregate(field_ty.clone());

                if let Some(aggr) = is_aggr {
                    Some((HIRPattern::new_wild_card(aggr, true, self.name(name)), false))
                } else {
                    Some((HIRPattern::new_wild_card(self.pass_ty(field_ty.clone())?, false, self.name(name)), false))
                }
            }
            Some(P::DeStructure { name, lkey_tok, fields, ignore, rkey_tok }) => {
                // put the names of the destructuring in the already known names
                self.pass_destructure_impl(
                    name,
                    lkey_tok,
                    fields.as_slice(),
                    ignore.as_ref(),
                    rkey_tok,
                    names,
                )
            }
            Some(other) => {
                // pass the pattern
                let (
                    other_hir,
                    other_is_reachable,
                    new_names
                ) = self.pass_pattern(
                    field_name.loc(),
                    other,
                    field_ty,
                )?;
                if other_is_reachable {
                    *is_reachable = true;
                }
                names.extend(new_names.into_iter());
                Some((
                    other_hir,
                    other_is_reachable
                ))
            }
            None => {
                // add name to names
                names.push((
                    field_name.clone(),
                    field_ty.clone(),
                    field_mutability.clone(),
                ));

                let is_aggr = self.type_is_aggregate(field_ty.clone());

                if let Some(aggr) = is_aggr {
                    Some((HIRPattern::new_wild_card(aggr, true, self.name(field_name)), false))
                } else {
                    Some((HIRPattern::new_wild_card(self.pass_ty(field_ty.clone())?, false, self.name(field_name)), false))
                }
            }
        }
    }

    /// Handles the destructuring of unions.
    fn handle_union_destructure(
        &mut self,
        name: &Identifier,
        fields: &[(Identifier, Type)],
        field: &(Mutability, Identifier, Option<Pattern>),
        names: &mut Vec<(Identifier, Type, Mutability)>,
    ) -> Option<(HIRPattern, bool)> {
        // this is much simpler than the struct one because
        // we only have to account for a single field instead
        // of many fields

        let mut is_reachable = false;

        // check if field exists
        if let Some((index, (_, field_ty))) = fields.iter().enumerate().find(|tuple| tuple.1.0 == field.1) {
            let (field_hir, is_reachable) = self.handle_aggregate_field_pattern(
                field.2.as_ref(),
                &field.0,
                &field.1,
                &mut is_reachable,
                field_ty,
                names
            )?;
            
            Some((
                HIRPattern::new_de_structure(
                    self.pass_ty(Type::new_named_type(name.clone()))?,
                    true,
                    vec![(self.name(&field.1), index, field_hir, self.pass_ty(field_ty.clone())?)],
                ),
                is_reachable
            ))
        } else {
            self.add_error(
                CheckerError::InvalidUnionField{ 
                    uni: name.clone(),
                    field: field.1.clone(),
                }
            );
            None
        }
    }

    /// Typechecks a slot declaration.
    fn pass_slot_decl(&mut self, name: &Identifier, ty: &Type, mutability: &Option<Loc>) -> Option<(Type, HIRExpr)> {
        if self.ctx.lookup_variable(&name.1).is_some() {
            // redeclaration of slot
            self.add_error(CheckerError::SlotRedefinition(name.clone()));

            // return none
            None
        } else if self.is_valueless_type(ty) {
            // cannot declare a zero sized slot
            self.add_error(CheckerError::CantHaveValuelessSlot(
                name.0.clone(),
                ty.clone(),
            ));

            // return none
            None
        } else {
            // declare slot
            self.ctx
                .declare_slot_in_current_scope(name.index(), ty.clone(), mutability.clone());
            // get the type of the slot for HIR
            let hir_ty = self.pass_ty(ty.clone())?;

            // return universe
            Some((
                Type::new_universe(),
                HIRExpr::SlotDecl(self.collection.unwrap_get(name.index()).to_string(), hir_ty),
            ))
        }
    }

    /// Returns `true` if this type is valueless.
    fn is_valueless_type(&self, ty: &Type) -> bool {
        return matches!(ty, Type::Void | Type::Universe);
    }

    /// Returns `Some` with the type if it is aggregate.
    fn type_is_aggregate(&mut self, ty: Type) -> Option<HIRType> {
        if let Type::NamedType(t) = &ty {
            if let Some(Member::Type(actt)) = self.ctx.lookup_member(&t.index()) {
                if let CtxUserType { ty: UserType::Struct(Struct { .. }), .. } = &*actt.borrow() {
                    Some(self.pass_ty(ty)?)
                } else if let CtxUserType { ty: UserType::Union(..), .. } = &*actt.borrow() {
                    Some(self.pass_ty(ty)?)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Returns if two types are the same.
    fn types_are_same(&mut self, at: &Loc, lhs: &Type, rhs: &Type) -> Option<bool> {
        match self.ctx.types_are_equal(at, lhs, rhs) {
            Either::Left(b) => Some(b),
            Either::Right(errors) => {
                for error in errors {
                    self.add_error(error);
                }
                None
            }
        }
    }

    /// Checks if a type supports the input
    /// binary operator.
    fn check_if_supports_operator(
        &mut self,
        at: Loc,
        ty: &Type,
        operator: &BinaryOp,
    ) -> Option<()> {
        if self.ctx.type_supports_bin_op(ty, operator) {
            Some(())
        } else {
            self.add_error(CheckerError::CantUseBinOpOnTy(
                at,
                operator.clone(),
                ty.clone(),
            ));
            None
        }
    }

    /// Verifies a return expression.
    fn pass_return_expr(&mut self, ret: &ReturnExpr) -> Option<(Type, Reachability, HIRExpr)> {
        let current_return_type = self.ctx.current_function_return_type();
        if let Some(expr) = &ret.expr {
            let (returned_type, _expr_reachability, hir_expr) =
                self.pass_expr(&expr, ExprState::IsExpr, Some(current_return_type.clone()))?;

            if let Type::Pointer { lifetime: Some(_), .. } = &returned_type {
                self.add_error(
                    CheckerError::CantReturnPtrToLocalResource(
                        ret.ret_kw.clone(),
                        returned_type.clone(),
                    )
                )
            }

            if current_return_type != returned_type {
                self.add_error(CheckerError::ReturningDiffTypeThanDecl {
                    at: ret.ret_kw.clone(),
                    decl: current_return_type.clone(),
                    ret: returned_type,
                });

                None
            } else {
                Some((
                    Type::Void,
                    Reachability::Unreachable,
                    HIRExpr::Return(HIRReturnExpr {
                        ret_kw: ret.ret_kw.clone(),
                        expr: Some(Box::new(hir_expr)),
                        aggregate: self.type_is_aggregate(current_return_type),
                    }),
                ))
            }
        } else if current_return_type != Type::Void {
            self.add_error(CheckerError::ReturningDiffTypeThanDecl {
                at: ret.ret_kw.clone(),
                decl: current_return_type.clone(),
                ret: Type::Void,
            });

            None
        } else {
            Some((
                current_return_type,
                Reachability::Unreachable,
                HIRExpr::Return(HIRReturnExpr {
                    ret_kw: ret.ret_kw.clone(),
                    expr: None,
                    aggregate: None,
                }),
            ))
        }
    }

    /// Gets the type of the variable
    fn get_type_of_var(&mut self, loc: &Loc, name: &NameIndex, set_init: bool) -> Option<Type> {
        if let Some((var, _)) = self.ctx.lookup_variable_mut(name) {
            let Variable { ty, init, .. } = var;

            // set to initialized if specified
            if set_init {
                *init = true;
            }

            if !*init {
                let ty = ty.clone();

                // accessing uninitialized slot
                self.error_or_warn(
                    RequiredState::UnsafeContext,
                    WarningOrError::AccessingUninitializedSlot(loc.clone(), *name, ty.clone()),
                );

                Some(ty)
            } else {
                // return okay if variable is init
                Some(ty.clone())
            }
        } else if let Some(Member::Function(func)) = self.ctx.lookup_member(name) {
            Some(Type::new_function_pointer(func.borrow().proto().clone()))
        } else {
            None
        }
    }

    /// Gets the type of the variable.
    ///
    /// If `set_init` os true, it sets the variable to an
    /// initialized state.
    /// 
    /// The `usize` item is the index of the scope of the
    /// variable at its declaration.
    fn get_var(
        &mut self,
        loc: &Loc,
        name: &NameIndex,
        set_init: bool,
        addrof: bool,
    ) -> Option<(Type, HIRExpr, Option<Loc>, bool, usize)> {
        if let Some(var) = self.ctx.lookup_variable_mut(name) {
            let (Variable {
                ty,
                init,
                is_argument,
                mutability,
            }, scope_index) = var;

            let was_init = *init;

            // set to initialized if specified
            if set_init {
                *init = true;
            }

            let var = Variable {
                ty: ty.clone(),
                init: *init,
                is_argument: *is_argument,
                mutability: mutability.clone(),
            };

            if !*init {
                let ty = ty.clone();

                // accessing uninitialized slot
                self.error_or_warn(
                    RequiredState::UnsafeContext,
                    WarningOrError::AccessingUninitializedSlot(loc.clone(), *name, ty.clone()),
                );

                Some((
                    ty.clone(),
                    if addrof {
                        HIRExpr::AsReference(HIRAsReferenceExpr(
                            loc.clone(),
                            Box::new(if let Some(index) = var.is_argument {
                                let param_ty = self.pass_ty(ty)?;
                                HIRExpr::new_argument(
                                    self.collection.unwrap_get(*name).to_string(),
                                    param_ty,
                                    index + self.type_is_aggregate(self.ctx.func_ret_ty()).map(|_| 1).unwrap_or_default(),
                                )
                            } else {
                                HIRExpr::Variable(
                                    self.collection.unwrap_get(*name).to_string(),
                                    self.pass_ty(ty)?,
                                )
                            }),
                        ))
                    } else {
                        if let Some(index) = var.is_argument {
                            let param_ty = self.pass_ty(ty)?;
                            HIRExpr::new_argument(
                                self.collection.unwrap_get(*name).to_string(),
                                param_ty,
                                index + self.type_is_aggregate(self.ctx.func_ret_ty()).map(|_| 1).unwrap_or_default(),
                            )
                        } else {
                            HIRExpr::Variable(
                                self.collection.unwrap_get(*name).to_string(),
                                self.pass_ty(ty)?,
                            )
                        }
                    },
                    if !var.init {
                        Some(Loc::default())
                    } else {
                        var.mutability
                    },
                    was_init,
                    scope_index,
                ))
            } else {
                // return okay if variable is init
                Some((
                    ty.clone(),
                    if addrof {
                        HIRExpr::AsReference(HIRAsReferenceExpr(
                            loc.clone(),
                            Box::new(if let Some(index) = var.is_argument {
                                let param_ty = self.pass_ty(var.ty)?;
                                HIRExpr::new_argument(
                                    self.collection.unwrap_get(*name).to_string(),
                                    param_ty,
                                    index + self.type_is_aggregate(self.ctx.func_ret_ty()).map(|_| 1).unwrap_or_default(),
                                )
                            } else {
                                HIRExpr::Variable(
                                    self.collection.unwrap_get(*name).to_string(),
                                    self.pass_ty(var.ty)?,
                                )
                            }),
                        ))
                    } else {
                        if let Some(index) = var.is_argument {
                            let param_ty = self.pass_ty(var.ty)?;
                            HIRExpr::new_argument(
                                self.collection.unwrap_get(*name).to_string(),
                                param_ty,
                                index + self.type_is_aggregate(self.ctx.func_ret_ty()).map(|_| 1).unwrap_or_default(),
                            )
                        } else {
                            HIRExpr::Variable(
                                self.collection.unwrap_get(*name).to_string(),
                                self.pass_ty(var.ty)?,
                            )
                        }
                    },
                    if !var.init {
                        Some(Loc::default())
                    } else {
                        var.mutability
                    },
                    was_init,
                    scope_index,
                ))
            }
        } else if let Some(Member::Function(func)) = self.ctx.lookup_member(name) {
            let passed_proto = self.pass_proto(func.borrow().proto(), &func);
            let ty = Type::new_function_pointer(func.borrow().proto().clone());
            let name_of_function = func.borrow().full_name(&self.collection);
            Some((ty, HIRExpr::GlobalFunc(name_of_function, passed_proto?), None, true, 0))
        } else {
            None
        }
    }

    /// If the required state is not met, a warning is
    /// generated. Otherwise, an error is generated.
    fn error_or_warn(&mut self, state: RequiredState, wor: WarningOrError) {
        if self.ctx.state_is_met(state) {
            self.add_warning(wor);
        } else {
            self.add_error(CheckerError::WarningAsError(wor));
        }
    }

    /// Adds an error we found during type checking
    /// to the vector of errors.
    fn add_error(&mut self, error: CheckerError) {
        self.errors.push(error);
    }

    /// Adds a warning we found during type checking
    /// to the vector of warnings.
    fn add_warning(&mut self, warning: WarningOrError) {
        self.warnings.push(warning);
    }

    fn name(&self, name: &Identifier) -> String {
        self.collection.unwrap_get(name.index()).to_string()
    }
}

/// Gets the type of binary operation from one of
/// its operands.
fn binary_operation_type_of(ty: &Type) -> BinOpType {
    if ty.is_int() {
        BinOpType::Int
    } else if ty.is_uint() {
        BinOpType::UInt
    } else if ty.is_float() {
        BinOpType::Float
    } else {
        unreachable!("Invalid type for getting type of binary operation: {ty:?}")
    }
}

/// The required state of the type checker for
/// the report be an error or a warning.
pub enum RequiredState {
    /// Be within an unsafe block of a function.
    UnsafeContext,
}

#[derive(Clone)]
/// If the statement is reachable or not.
pub enum Reachability {
    /// Anything is from now on is reachable.
    Reachable,
    /// Anything from now on is unreachable.
    Unreachable,
}

impl Reachability {
    /// Returns if this is reachable.
    pub fn reachable(&self) -> bool {
        matches!(self, Self::Reachable)
    }
    /// Returns if this is unreachable.
    pub fn unreachable(&self) -> bool {
        matches!(self, Self::Unreachable)
    }
}

impl BitAnd for Reachability {
    type Output = Reachability;

    fn bitand(self, rhs: Self) -> Self::Output {
        if matches!(self, Self::Unreachable) & matches!(rhs, Self::Unreachable) {
            Self::Unreachable
        } else {
            Self::Reachable
        }
    }
}

impl BitAndAssign for Reachability {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = self.clone() & rhs;
    }
}

#[derive(Debug)]
/// An error generated during type checking.
pub enum CheckerError {
    /// An error when adding a member to a namespace.
    AddMember(Loc, AddMemberError),
    /// Invalid use of an expression as a statement.
    InvalidExpressionAsStatement(Loc, &'static str),
    /// Invalid use of an expression as a value.
    InvalidExpressionAsValue(Loc, &'static str),
    /// Cannot take address of rvalue expression.
    CantTakeAddrOfRvalExpr(Loc),
    /// Int literal too big for target type.
    LitTooBigForTy(IntLit, Type, u64),
    /// Member not found
    MemberNotFound(Loc, NameIndex),
    /// Cannot use a binary operator on different types.
    BinOnDiffTys(Loc, Type, Type),
    /// Type does not support binary operator.
    CantUseBinOpOnTy(Loc, BinaryOp, Type),
    /// Call non function type.
    CallNonFunc(Loc, Type),
    /// Function got different param size than it was expecting.
    FuncGotDiffParamSizeThanInProto {
        call_at: Loc,
        in_proto: usize,
        received: usize,
        type_of_func_is: Type,
    },
    /// Param expected one type but received another.
    WrongParamTy {
        param: NameIndex,
        expected: Type,
        received: Type,
        expr_loc: Loc,
    },
    /// Assigning wrong type
    AssignWrongTy {
        slot_ty: Type,
        expr_loc: Loc,
        expr_ty: Type,
    },
    /// Assigning to a constant reference.
    ChangeConst {
        lvalue_ty: Type,
        loc: Loc,
    },
    /// Use of undefined name.
    UndefinedName(Identifier),
    /// Slot redefinition.
    SlotRedefinition(Identifier),
    /// Cannot set slot to valueless type.
    CantHaveValuelessSlot(Loc, Type),
    /// Warning as error.
    WarningAsError(WarningOrError),
    /// Everything from now on is unreachable.
    StmtIsUnreachable(Loc),
    /// Returning different type than the
    /// one declared.
    ReturningDiffTypeThanDecl { at: Loc, decl: Type, ret: Type },
    /// Using unreachable expression as value.
    UsingUnreachableExprAsVal(Loc),
    /// Function which expected to return a value.
    DoesNotRetInAllPathsButMust { loc: Loc, expected_ty: Type },
    /// Condition is not bool.
    CondIsntBool(Loc, Type),
    /// Array of zero sized type.
    ZeroSizedTypeArray(Loc, Type),
    /// Array with negative size.
    NegativeSizedArray(Loc, IntLit),
    /// Struct field redefinition.
    StructFieldRedefinition {
        name: Identifier,
        field: Identifier,
        for_: &'static str,
    },
    /// This named type was not found
    /// in the current namespace.
    NamedTypeNotFound(Identifier),
    /// Accessing property of non-struct
    /// type.
    AccPropOfNonAggrTy(Loc, Type),
    /// Property does not exist at the
    /// struct specified.
    NoSuchPropAtStruct(Type, Identifier),
    /// Generic function not found
    GenericFunctionNotFound(Identifier),
    /// Invalid template parameter length.
    InvalidTemplParamLen {
        name: Identifier,
        expected: usize,
        found: usize,
    },
    /// Instantiating non struct type.
    InstantiatingNonStructType(Identifier),
    /// Wrong number of fields for struct.
    WrongFieldNumberForStruct {
        name: Identifier,
        received: usize,
        needed: usize,
    },
    /// Field not provided.
    FieldNotProvidedWhenInstantiating {
        struct_name: Identifier,
        field: Identifier,
        ty: Type,
    },
    /// Repeated field in instantiation.
    RepeatedFieldInInstantiation {
        field: Identifier,
        provided: usize,
    },
    /// Wrong type for field
    WrongTyForField {
        struct_name: Identifier,
        field_name: Identifier,
        supplied_ty: Type,
        expected_ty: Type,
        instantiating: &'static str,
    },
    /// Dereference non ptr type.
    DerefNonPtrTy(Loc, Type),
    /// Only one field can be specified when 
    /// instantiating an union.
    UnionMultipleFieldInstantiation(Loc),
    /// The union type does not have a field
    /// named this.
    InvalidUnionField {
        uni: Identifier,
        field: Identifier
    },
    /// Integer type does not support negative
    /// numbers.
    IntTyNonNeg(IntLit, Type),
    /// Lifetime of pointer assigned to variable
    /// is smaller than the lifetime of the variable
    /// itself.
    LifetimeOfVariableGreaterThanOfPointer(Loc, Type, Type),
    /// Cannot return a pointer to local resources.
    CantReturnPtrToLocalResource(Loc, Type),
    /// Pattern is not valid for the switched on value.
    InvalidPatForTy {
        loc: Loc,
        switched_on: Type,
        pattern_ty: Type,
    },
    /// Type of range start is different than the one
    /// of the range end.
    RangeEndsTyDiff {
        begin_ty: Type,
        range: Loc,
        end_ty: Type,
    },
    /// Literal type does not support range matching.
    LitDoesntSupportRange(Loc, Type),
    /// Left value of range has a bigger value than
    /// the one in the right.
    LeftGreaterThanRightInRange(Loc),
    /// Range exclusive can't have left value equal
    /// to the right value.
    RangeExclusiveWithEqualEnds(Loc),
    /// Struct fields were not matched in pattern.
    StructFieldsNotMatchedInPat {
        name: Identifier,
        expected: usize,
        found: usize,
    },
    /// Too many struct fields specified in pattern.
    TooManyStructFieldsMatchedInPat {
        name: Identifier,
        expected: usize,
        found: usize,
    },
    /// No fields provided for union pattern.
    NoFieldsSpecifiedToUnionPattern {
        name: Identifier,
    },
    /// Too many fields specified for union
    /// pattern.
    TooManyFieldsSpecifiedForUnionPattern {
        name: Identifier,
        amount: usize,
    },
    /// Cannot match on aliased types.
    MatchingOnAlias(Identifier),
    /// Unreachable case pattern.
    UnreachableCasePattern(Loc),
    /// Not all patterns matched for type.
    NotAllPatsMatchedForTy(Loc, Type),
    /// Method not found for aggregate type.
    MethodNotFoundForAggr {
        aggr: Identifier,
        method: Identifier,
    },
    /// Call method which takes by-value receiver
    /// on a pointer.
    CallMethodWhichTakesByValueRecOnPtr {
        aggr: Identifier,
        method: Identifier,
    },
    /// Invalid type as receiver.
    InvalidTypeAsReceiver(Identifier, Type),
    /// Type must be defined at the time
    /// of definition for receiver.
    TypeMustBeDefinedAtTimeOfDefinitionForReceiver {
        function: Identifier,
        name: Identifier,
    },
    /// Method redefiniton for struct.
    MethodRedefinition {
        aggr: Identifier,
        name: Identifier,
    },
    /// Must specify variant when destructuring a
    /// sum type.
    MustSpecifyVariantDestructSumTy(Identifier),
    /// The index of the discriminant has already
    /// appeared before.
    RepeatedSumTyDiscriminant {
        sum_ty: Identifier,
        variant: Identifier,
        before: Identifier,
        discriminant: u64,
    },
    /// No such sum type variant.
    NoSuchSumVariant {
        sum: Identifier,
        variant: Identifier,
    },
    /// The sum type does not take
    /// variants.
    VariantDoesntTakeFields {
        sum: Identifier,
        variant: Identifier
    },
    /// The sum type takes fields but they
    /// were not specified.
    VariantTakeFieldsButNotFound {
        sum: Identifier,
        variant: Identifier
    },
}

impl CheckerError {
    pub fn to_string(&self, collection: &Collection) -> String {
        use CheckerError as CE;
        Color::Blue.bold().paint(match self {
            CE::AddMember(loc, addmember) => {
                format!(
                    "{}Error: {}",
                    loc_to_string(loc, collection),
                    match addmember {
                        AddMemberError::AlreadyExists(name, _member) => {
                            format!(
                                "[EE002] The name '{}' already exists inside the namespace",
                                collection.unwrap_get(*name),
                            )
                        }
                        AddMemberError::ChildCollision(name, _member) => {
                            format!(
                                "[EE003] vThe name '{}' collides with a child namespace of the same name",
                                collection.unwrap_get(*name)
                            )
                        }
                    }
                )
            }
            CE::InvalidExpressionAsStatement(loc, msg) => {
                format!(
                    "{}Error: [EE004] Invalid use of expression as statement: {}",
                    loc_to_string(loc, collection),
                    msg
                )
            }
            CE::InvalidExpressionAsValue(loc, msg) => {
                format!(
                    "{}Error: [EE005] Invalid use of expression as value: {}",
                    loc_to_string(loc, collection),
                    msg
                )
            }
            CE::CantTakeAddrOfRvalExpr(loc) => {
                format!(
                    "{}Error: [EE006] Cannot take address of an rvalue",
                    loc_to_string(loc, collection)
                )
            }
            CE::LitTooBigForTy(lit, ty, maxvalue) => {
                format!(
                    "{}Error: [EE007] Literal '{}' too big for type '{}' which has a maximum possible value of '{maxvalue}'",
                    loc_to_string(&lit.0, collection),
                    lit.1,
                    ty_to_string(ty, collection)
                )
            }
            CE::MemberNotFound(loc, name) => {
                format!(
                    "{}Error: [EE008] Member '{}' not found",
                    loc_to_string(loc, collection),
                    collection.unwrap_get(*name)
                )
            }
            CE::BinOnDiffTys(loc, lhs, rhs) => {
                format!(
                    "{}Error: [EE009] Cannot use binary operator on different types '{}' and '{}'",
                    loc_to_string(loc, collection),
                    ty_to_string(lhs, collection),
                    ty_to_string(rhs, collection),
                )
            }
            CE::CallNonFunc(loc, ty) => {
                format!(
                    "{}Error: [EE010] Cannot call non-function type '{}'",
                    loc_to_string(loc, collection),
                    ty_to_string(ty, collection)
                )
            }
            CE::FuncGotDiffParamSizeThanInProto { call_at, in_proto, received, type_of_func_is } => {
                format!(
                    "{}Error: [EE011] The type '{}' specifies '{in_proto}' arguments but '{received}' parameters were given to the call",
                    loc_to_string(call_at, collection),
                    ty_to_string(type_of_func_is, collection)
                )
            }
            CE::WrongParamTy { param, expected, received, expr_loc } => {
                format!(
                    "{}Error: [EE012] Wrong type for parameter '{}': expected type '{}' but received type '{}'",
                    loc_to_string(expr_loc, collection),
                    collection.unwrap_get(*param),
                    ty_to_string(expected, collection),
                    ty_to_string(received, collection),
                )
            }
            CE::AssignWrongTy { slot_ty, expr_loc, expr_ty } => {
                format!(
                    "{}Error: [EE013] Cannot assign to an lvalue of type '{}' a value of type '{}'",
                    loc_to_string(expr_loc, collection),
                    ty_to_string(slot_ty, collection),
                    ty_to_string(expr_ty, collection),
                )
            }
            CE::ChangeConst { lvalue_ty, loc } => {
                format!(
                    "{}Error: [EE014] Cannot assign to constant lvalue reference type '{}'",
                    loc_to_string(loc, collection),
                    ty_to_string(lvalue_ty, collection)
                )
            }
            CE::UndefinedName(name) => {
                format!(
                    "{}Error: [EE015] Undefined name '{}'",
                    loc_to_string(&name.0, collection),
                    collection.unwrap_get(name.1),
                )
            }
            CE::CantUseBinOpOnTy(loc, op, ty) => {
                format!(
                    "{}Error: [EE016] Binary operator '{}' cannot be used in instance of type '{}'",
                    loc_to_string(loc, collection),
                    op.to_string(),
                    ty_to_string(ty, collection),
                )
            }
            CE::SlotRedefinition(name) => {
                format!(
                    "{}Error: [EE017] Can't redefine the named slot '{}'",
                    loc_to_string(&name.0, collection),
                    collection.unwrap_get(name.1),
                )
            }
            CE::CantHaveValuelessSlot(loc, ty) => {
                format!(
                    "{}Error: [EE018] Cannot use the valueless type '{}' as the type of a slot",
                    loc_to_string(loc, collection),
                    ty_to_string(ty, collection),
                )
            }
            CE::WarningAsError(wor) => {
                wor.to_string(
                    collection,
                    false
                )
            }
            CE::StmtIsUnreachable(loc) => {
                format!(
                    "{}Error: [EE019] Everything from now on is unreachable",
                    loc_to_string(loc, collection)
                )
            }
            CE::ReturningDiffTypeThanDecl { at: loc, decl, ret } => {
                format!(
                    "{}Error: [EE020] Returned type '{}' does not match expected return type '{}' specified in function prototype",
                    loc_to_string(loc, collection),
                    ty_to_string(ret, collection),
                    ty_to_string(decl, collection),
                )
            }
            CE::UsingUnreachableExprAsVal(loc) => {
                format!(
                    "{}Error: [EE021] Unreachable expression cannot be used as a value",
                    loc_to_string(loc, collection),
                )
            }
            CE::DoesNotRetInAllPathsButMust { loc, expected_ty } => {
                format!(
                    "{}Error: [EE022] Function declared to return non-valueless type '{}', but a value is not returned in all code paths",
                    loc_to_string(loc, collection),
                    ty_to_string(expected_ty, collection),
                )
            }
            CE::CondIsntBool(loc, cond) => {
                format!(
                    "{}Error: [EE023] Value of type '{}' was used as a condition but a value of type 'bool' was expected",
                    loc_to_string(loc, collection),
                    ty_to_string(cond, collection)
                )
            }
            CE::ZeroSizedTypeArray(loc, subty) => {
                format!(
                    "{}Error: [EE024] Valueless type '{}' cannot be used as an element type for sized arrays",
                    loc_to_string(loc, collection),
                    ty_to_string(subty, collection)
                )
            }
            CE::NegativeSizedArray(loc, len) => {
                format!(
                    "{}Error: [EE025] Negative integer '{}' cannot be used as the size of an array",
                    loc_to_string(loc, collection),
                    len.1
                )
            }
            CE::StructFieldRedefinition { name, field, for_ } => {
                format!(
                    "{}Error: [EE026] Redefinition of field '{}' for {for_} '{}'",
                    loc_to_string(field.loc(), collection),
                    collection.unwrap_get(field.index()),
                    collection.unwrap_get(name.index()),
                )
            }
            CE::NamedTypeNotFound(ty) => {
                format!(
                    "{}Error: [EE027] Named type '{}' was not found within the current namespace",
                    loc_to_string(ty.loc(), collection),
                    collection.unwrap_get(ty.index())
                )
            }
            CE::AccPropOfNonAggrTy(loc, ty) => {
                format!(
                    "{}Error: [EE028] Cannot access property of non-aggregate type '{}'",
                    loc_to_string(loc, collection),
                    ty_to_string(ty, collection),
                )
            }
            CE::NoSuchPropAtStruct(ty, prop) => {
                format!(
                    "{}Error: [EE029] Struct '{}' doesn't have a property named '{}'",
                    loc_to_string(prop.loc(), collection),
                    ty_to_string(ty, collection),
                    collection.unwrap_get(prop.index()),
                )
            }
            CE::GenericFunctionNotFound(name) => {
                format!(
                    "{}Error: [EE030] Generic function '{}' was not found",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                )
            }
            CE::InvalidTemplParamLen { name, expected, found } => {
                format!(
                    "{}Error: [EE031] Generic function '{}' expected {} template arguments but received {}",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                    expected,
                    found,
                )
            }
            CE::InstantiatingNonStructType(ty) => {
                format!(
                    "{}Error: [EE032] Could not instantiate the type '{}' as it is not a structure",
                    loc_to_string(ty.loc(), collection),
                    collection.unwrap_get(ty.index()),
                )
            }
            CE::WrongFieldNumberForStruct { name, received, needed } => {
                format!(
                    "{}Error: [EE033] Struct '{}' expected {} fields but received {} during instantiation",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                    needed,
                    received,
                )
            }
            CE::FieldNotProvidedWhenInstantiating { struct_name, field, ty } => {
                format!(
                    "{}Error: [EE034] When instantiating the struct '{}' the field '{}' of type '{}' was not provided",
                    loc_to_string(field.loc(), collection),
                    collection.unwrap_get(struct_name.index()),
                    collection.unwrap_get(field.index()),
                    ty_to_string(ty, collection),
                )
            }
            CE::RepeatedFieldInInstantiation { field, provided } => {
                format!(
                    "{}Error: [EE035] Field '{}' was provided {} times instead of one",
                    loc_to_string(field.loc(), collection),
                    collection.unwrap_get(field.index()),
                    provided,
                )
            }
            CE::WrongTyForField { struct_name, field_name, supplied_ty, expected_ty, instantiating } => {
                format!(
                    "{}Error: [EE036] The type '{}' was expected for the field '{}' but '{}' was received when instantiating the {instantiating} '{}'",
                    loc_to_string(field_name.loc(), collection),
                    ty_to_string(expected_ty, collection),
                    collection.unwrap_get(field_name.index()),
                    ty_to_string(supplied_ty, collection),
                    collection.unwrap_get(struct_name.index()),
                )
            }
            CE::DerefNonPtrTy(deref_tok, base) => {
                format!(
                    "{}Error: [EE037] Cannot dereference the non-pointer type '{}'",
                    loc_to_string(deref_tok, collection),
                    ty_to_string(base, collection),
                )
            }
            CE::UnionMultipleFieldInstantiation(loc) => {
                format!(
                    "{}Error: [EE038] Only one field can be specified when instantiating an union",
                    loc_to_string(loc, collection),
                )
            }
            CE::InvalidUnionField { uni, field } => {
                format!(
                    "{}Error: [EE039] Invalid field '{}' for union '{}'",
                    loc_to_string(field.loc(), collection),
                    collection.unwrap_get(field.index()),
                    collection.unwrap_get(uni.index()),
                )
            }
            CE::IntTyNonNeg(lit, ty) => {
                format!(
                    "{}Error: [EE040] Type '{}' does not support negative numbers: '{}'",
                    loc_to_string(&lit.0, collection),
                    ty_to_string(ty, collection),
                    lit.2,
                )
            }
            CE::LifetimeOfVariableGreaterThanOfPointer(ampersand, variable_ty, pointer_ty) => {
                format!(
                    "{}Error: [EE041] Cannot assign a pointer '{}' to something of type '{}' whose lifetime is greater than the one of the assigned pointer",
                    loc_to_string(ampersand, collection),
                    ty_to_string(pointer_ty, collection),
                    ty_to_string(variable_ty, collection),
                )
            }
            CE::CantReturnPtrToLocalResource(ret_kw, ty) => {
                format!(
                    "{}Error: [EE042] Cannot return from function a pointer of type '{}' which points to a resource only available locally",
                    loc_to_string(ret_kw, collection),
                    ty_to_string(ty, collection),
                )
            }
            CE::InvalidPatForTy { loc, switched_on, pattern_ty } => {
                format!(
                    "{}Error: [EE043] Switched on value is of type '{}' but pattern requires a value of type '{}'",
                    loc_to_string(loc, collection),
                    ty_to_string(switched_on, collection),
                    ty_to_string(pattern_ty, collection),
                )
            }
            CE::RangeEndsTyDiff { begin_ty, range, end_ty } => {
                format!(
                    "{}Error: [EE044] Types from beginning of the range ('{}') and from the end of the range ('{}') differ",
                    loc_to_string(range, collection),
                    ty_to_string(begin_ty, collection),
                    ty_to_string(end_ty, collection),
                )
            }
            CE::LitDoesntSupportRange(loc, ty) => {
                format!(
                    "{}Error: [EE045] Literal of type '{}' doesn't support being in a range",
                    loc_to_string(loc, collection),
                    ty_to_string(ty, collection),
                )
            }
            CE::LeftGreaterThanRightInRange(loc) => {
                format!(
                    "{}Error: [EE046] Left side cannot be greater than the right side in a range",
                    loc_to_string(loc, collection),
                )
            }
            CE::RangeExclusiveWithEqualEnds(loc) => {
                format!(
                    "{}Error: [EE047] Range exclusive does not allow for both ends to be equal",
                    loc_to_string(loc, collection)
                )
            }
            CE::StructFieldsNotMatchedInPat { name, expected, found } => {
                format!(
                    "{}Error: [EE048] Too little fields were found when matching the struct '{}': {} fields were expected but {} were found",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                    expected,
                    found,
                )
            }
            CE::TooManyStructFieldsMatchedInPat { name, expected, found } => {
                format!(
                    "{}Error: [EE048] Too many fields were found when matching the struct '{}': {} fields were expected but {} were found",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                    expected,
                    found,
                )
            }
            CE::NoFieldsSpecifiedToUnionPattern { name } => {
                format!(
                    "{}Error: [EE049] No fields specified when matching union '{}'",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                )
            }
            CE::TooManyFieldsSpecifiedForUnionPattern { name, amount } => {
                format!(
                    "{}Error: [EE050] Too many fields specified when matching the union '{}': expected only one but found '{}'",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                    amount
                )
            }
            CE::MatchingOnAlias(name) => {
                format!(
                    "{}Error: [EE051] Cannot pattern match using '{}' which is an alias",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                )
            }
            CE::UnreachableCasePattern(loc) => {
                format!(
                    "{}Error: [EE052] Case pattern is unreachable",
                    loc_to_string(loc, collection),
                )
            }
            CE::MethodNotFoundForAggr { aggr, method } => {
                format!(
                    "{}Error: [EE053] Method '{}' not found in aggregate type '{}'",
                    loc_to_string(method.loc(), collection),
                    collection.unwrap_get(method.index()),
                    collection.unwrap_get(aggr.index()),
                )
            }
            CE::CallMethodWhichTakesByValueRecOnPtr { aggr, method } => {
                format!(
                    "{}Error: [EE054] Cannot call method '{}' of aggregate type '{}' which takes receiver by-value on pointer",
                    loc_to_string(method.loc(), collection),
                    collection.unwrap_get(method.index()),
                    collection.unwrap_get(aggr.index()),
                )
            }
            CE::InvalidTypeAsReceiver(name, ty) => {
                format!(
                    "{}Error: [EE055] Invalid type as receiver: '{}'",
                    loc_to_string(name.loc(), collection),
                    ty_to_string(ty, collection),
                )
            }
            CE::TypeMustBeDefinedAtTimeOfDefinitionForReceiver { function, name } => {
                format!(
                    "{}Error: [EE056] Receiver type '{}' of function '{}' must be defined at the time where the function is defined",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                    collection.unwrap_get(function.index()),
                )
            }
            CE::MethodRedefinition { aggr, name } => {
                format!(
                    "{}Error: [EE057] Method redefinition for '{}' of type '{}'",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                    collection.unwrap_get(aggr.index()),
                )
            }
            CE::NotAllPatsMatchedForTy(loc, ty) => {
                format!(
                    "{}Error: [EE058] Not all patterns matched for type '{}' in switch statement",
                    loc_to_string(loc, collection),
                    ty_to_string(ty, collection),
                )
            }
            CE::MustSpecifyVariantDestructSumTy(loc) => {
                format!(
                    "{}Error: [EE059] Must specify a variant when destructing a sum type",
                    loc_to_string(loc.loc(), collection),
                )
            }
            CE::RepeatedSumTyDiscriminant { sum_ty, variant, before, discriminant } => {
                format!(
                    "{}Error: [EE060] The discriminant '{}' previously used by the variant '{}' was used again by a variant named '{}' in the sum type '{}', which is not allowed",
                    loc_to_string(variant.loc(), collection),
                    discriminant,
                    collection.unwrap_get(before.index()),
                    collection.unwrap_get(variant.index()),
                    collection.unwrap_get(sum_ty.index()),
                )
            }
            CE::NoSuchSumVariant { sum, variant } => {
                format!(
                    "{}Error: [EE061] The variant '{}' does not exist within the sum type '{}'",
                    loc_to_string(variant.loc(), collection),
                    collection.unwrap_get(variant.index()),
                    collection.unwrap_get(sum.index()),
                )
            }
            CE::VariantDoesntTakeFields { sum, variant } => {
                format!(
                    "{}Error: [EE062] The variant '{}' of the sum type '{}' does not take fields",
                    loc_to_string(variant.loc(), collection),
                    collection.unwrap_get(variant.index()),
                    collection.unwrap_get(sum.index()),
                )
            }
            CE::VariantTakeFieldsButNotFound { sum, variant } => {
                format!(
                    "{}Error: [EE063] The variant '{}' of the sum type '{}' takes fields but none were found",
                    loc_to_string(variant.loc(), collection),
                    collection.unwrap_get(variant.index()),
                    collection.unwrap_get(sum.index()),
                )
            }
        }).to_string()
    }
}

fn loc_to_string(loc: &Loc, collection: &Collection) -> String {
    format!(
        "\"{}\":{}:{}: ",
        collection.get(*loc.file()).unwrap(),
        loc.line() + 1,
        loc.column() + 1,
    )
}

fn ty_to_string(ty: &Type, collection: &Collection) -> String {
    use Type as T;
    match ty {
        T::Primitive { loc, ty } => match ty {
            PrimType::Bool => "bool",
            PrimType::Int(i) => match i {
                TypeBits::B8 => "i8",
                TypeBits::B16 => "i16",
                TypeBits::B32 => "i32",
                TypeBits::B64 => "i64",
            },
            PrimType::UInt(i) => match i {
                TypeBits::B8 => "u8",
                TypeBits::B16 => "u16",
                TypeBits::B32 => "u32",
                TypeBits::B64 => "u64",
            },
            PrimType::Float(i) => match i {
                TypeBits::B32 => "f32",
                TypeBits::B64 => "f64",
                _ => todo!(),
            },
        }
        .to_string(),
        T::NamedType(ty) => collection.unwrap_get(ty.index()).to_string(),
        T::Instantiated { name, lbrac: _, instantiated, rbrac: _ } => {
            format!(
                "{}[{}]",
                collection.unwrap_get(name.index()),
                instantiated.iter()
                    .map(|t| ty_to_string(t, collection))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        T::Void => "void".to_string(),
        T::Universe => "universe".to_string(),
        T::SizedArray {
            left_bracket: _,
            size,
            of: _,
            element_type,
            right_bracket: _,
        } => {
            format!("[{} of {}]", size.1, ty_to_string(element_type, collection))
        }
        T::Pointer { pointee, mutability, lifetime } => format!(
            "{}*{}{}",
            if mutability.is_some() {
                "mut "
            } else {
                ""
            },
            ty_to_string(pointee, collection),
            if let Some(lifetime) = lifetime {
                format!(" @{lifetime}")
            } else {
                "".to_string()
            },
        ),
        T::FunctionPointer(proto) => format!(
            "func({}) {}",
            proto
                .arguments()
                .iter()
                .map(|arg| ty_to_string(&arg.ty, collection))
                .collect::<Vec<_>>()
                .join(", "),
            ty_to_string(proto.return_type(), collection)
        ),
        T::Tuple(ts) => {
            format!(
                "({})",
                ts
                    .iter()
                    .map(|ty| ty_to_string(&ty, collection))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        },
    }
}

#[derive(Debug)]
/// Can be both a warning or
pub enum WarningOrError {
    /// Using an uninitialized slot.
    AccessingUninitializedSlot(Loc, NameIndex, Type),
    /// Loop only runs once.
    LoopOnlyExecutesOnce(Loc),
}

impl WarningOrError {
    pub fn to_string(&self, collection: &Collection, is_warning: bool) -> String {
        let prologue = if is_warning { "Warning" } else { "Error" };
        use WarningOrError as WOR;
        (if is_warning {
            Color::Yellow.bold()
        } else {
            Color::Blue.bold()
        }).paint(match self {
            WOR::AccessingUninitializedSlot(loc, name, ty) => {
                format!(
                    "{}{prologue}: [WE001] Accessing uninitialized slot '{}' of type '{}' before assignment",
                    loc_to_string(loc, collection),
                    collection.unwrap_get(*name),
                    ty_to_string(ty, collection),
                )
            }
            WOR::LoopOnlyExecutesOnce(loc) => {
                format!(
                    "{}{prologue}: [WE002] Loop body only executes once",
                    loc_to_string(loc, collection),
                )
            }
        }).to_string()
    }
}

/// The result of passing through a case.
pub struct CaseResult {
    /// This case in HIR.
    case: HIRCase,
    /// If the pattern is reachable (allows for more cases).
    pattern_is_reachable: bool,
    /// If the block is reachable (e.g., for example, we return from it).
    block_is_reachable: Reachability,
}
