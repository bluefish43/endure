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
    cell::RefCell, collections::HashMap, fmt::Display, ops::{Add, BitAnd, BitAndAssign, BitOr}, rc::Rc
};

use ansi_term::Color;
use derive_getters::Getters;
use derive_new::new;
use either::Either;

use crate::{
    ast::{
        expr::{
            self, AsReferenceExpr, AssignmentExpr, BinaryExpr, BinaryOp, CallExpr, Conditional,
            Expr, LiteralExpr, ReturnExpr, WhileLoop,
        }, generics::Generic, tdecl::{TypeDecl, UserType}, typing::{NameIndex, PrimType, Type, TypeBits}, Block, Collection, Decl, FunctionDecl, Identifier, IntLit, Loc, NamespaceDecl, Prototype
    },
    check::{hir::HIRArgument, namespaces::Member},
};

use self::{
    ctx::Context,
    hir::{
        expr::{
            BinOpType, HIRAsReferenceExpr, HIRAssignmentExpr, HIRBinaryExpr, HIRCallExpr,
            HIRConditional, HIRExpr, HIRReturnExpr, HIRWhileLoop,
        },
        typing::HIRType,
        HIRBlock, HIRDecl, HIRFunctionDecl, HIRPrototype,
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
    instantiated: Vec<Vec<Type>>,
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

                if fdecl.prototype.generics().is_none() {
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
            .add_function_scope(prototype.arguments(), *prototype.unsafety());
        let (reachability, hirblock) = self.pass_block(block)?;

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
            UserType::Struct { fields } => {
                let mut occurred_fields = vec![];

                for (field_name, field_ty) in fields.iter() {
                    if occurred_fields.contains(&field_name.index()) {
                        self.add_error(
                            CheckerError::StructFieldRedefinition {
                                name: name.clone(),
                                field: field_name.clone(),
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
        // TODO: Implement namespace declaration typechecking

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
    fn pass_block(&mut self, block: &Block) -> Option<(Reachability, HIRBlock)> {
        let mut reachable = Reachability::Reachable;
        let mut hirblock_contents = vec![];
        let mut altered = false;
        for expr in block.stmts().iter() {
            if let Reachability::Unreachable = reachable {
                // unreachable code found
                self.add_error(CheckerError::StmtIsUnreachable(expr.loc()));
                break;
            }
            match self.pass_expr(expr, ExprState::IsStmt) {
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
        if !altered {
            Some((reachable, HIRBlock::new(hirblock_contents)))
        } else {
            None
        }
    }

    /// Validates a prototype.
    fn pass_proto(&mut self, proto: &Prototype, func: &ActFunction) -> Option<HIRPrototype> {
        // TODO: Type check the prototype

        let Prototype {
            name,
            arguments,
            return_type,
            ..
        } = proto;

        let mut error = false;

        let mut new_arguments = vec![];
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
                of,
                element_type,
                right_bracket,
            } => {
                // array of zero sized elements is not allowed
                if self.is_valueless_type(&element_type) {
                    self.add_error(CheckerError::ZeroSizedTypeArray(
                        left_bracket,
                        *element_type,
                    ));

                    None
                } else if size.1.is_negative() {
                    self.add_error(CheckerError::NegativeSizedArray(size.0.clone(), size));

                    None
                } else {
                    let subtype = self.pass_ty(*element_type)?;

                    Some(HIRType::new_sized_array(size, Box::new(subtype)))
                }
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
            Type::Pointer { pointee, mutability } => Some(HIRType::new_pointer(
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
                        UserType::Struct { fields } => {
                            let mut hir_fields = Vec::with_capacity(fields.len());

                            for (_, field_ty) in fields.iter(){ 
                                hir_fields.push(self.pass_ty(field_ty.clone())?);
                            }

                            Some(HIRType::Struct(hir_fields))
                        }
                    }
                } else {
                    self.add_error(
                        CheckerError::NamedTypeNotFound(name)
                    );

                    None
                }
            }
            Type::Instantiated { name, lbrac, instantiated, rbrac } => {
                // TODO: Implement instantiated named types
                unimplemented!()
            }
        }
    }

    /// Passes through an expression which gives out
    /// an error if the expression is unreachable.
    fn pass_reachable_expr(&mut self, expr: &Expr, state: ExprState) -> Option<(Type, HIRExpr)> {
        let res = self.pass_expr(expr, state)?;

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
    ) -> Option<(Type, Reachability, HIRExpr)> {
        let prim: Option<(Type, HIRExpr)> = match expr {
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
                    self.pass_lit_expr(lit)
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
            Expr::AccessProperty(base, dot, prop) => self.pass_access_property(base, dot.clone(), prop),
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
        let (reachability, hirblock) = self.pass_block(block)?;

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
            let (reachability_of_if, hir_if_block) = self.pass_block(then)?;
            let (reachability_of_else, hir_else_block) = self.pass_block(&else_part.1)?;
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
            let (_, hir_if_block) = self.pass_block(then)?;

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
            self.pass_reachable_expr(condition, ExprState::IsExpr)?;

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
                let (var_ty, var_expr, var_mut, var_was_init) = self.get_var(
                    variable_name.loc(),
                    &variable_name.index(),
                    set_init,
                    set_init,
                )?;
                if let ExprState::IsAssignmentLhs = state {
                    if !var_was_init {
                        // return mutable pointer if variable is not
                        // initialized
                        return Some((Type::new_pointer(Box::new(var_ty), Some(Loc::default())), var_expr))
                    }
                }
                Some((Type::new_pointer(Box::new(var_ty), var_mut), var_expr))
            }
            Expr::AccessProperty(base, dot, ident) => {
                let (ty, expr) = self.pass_access_property(base, dot.clone(), ident)?;
                Some((Type::new_pointer(Box::new(ty), Some(Loc::default())), expr))
            }
            _ => {
                // Taking address of non-lvalue reference
                self.add_error(CheckerError::CantTakeAddrOfRvalExpr(ampersand.clone()));
                None
            }
        }
    }

    /// Validates a literal expression.
    fn pass_lit_expr(&mut self, expr: &LiteralExpr) -> Option<(Type, HIRExpr)> {
        match expr {
            LiteralExpr::Int(i) => {
                // return an int type
                Some((
                    Type::new_primitive(i.0.clone(), PrimType::new_int(TypeBits::B64)),
                    HIRExpr::Literal(expr.clone()),
                ))
            }
        }
    }

    /// Validastes the dereferencing of a pointer.
    fn pass_dereference_expr(&mut self, deref: &Loc, base: &Expr) -> Option<(Type, HIRExpr)> {
        let (base_ty, base_hir) = self.pass_reachable_expr(base, ExprState::IsExpr)?;

        if let Type::Pointer { pointee, mutability: _ } = &base_ty {
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
                UserType::Struct { fields } => {
                    let struct_ty = self.pass_ty(Type::NamedType(struct_name.clone()))?;

                    if expr_fields.len() != fields.len() {
                        self.add_error(CheckerError::WrongFieldNumberForStruct {
                            name: struct_name.clone(),
                            received: expr_fields.len(),
                            needed: fields.len(),
                        });

                        None
                    } else {
                        // check for each field
                        let mut hir_fields = Vec::new();

                        for (index, field) in fields.iter().enumerate() {
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
                                let (spec_field_ty, spec_field_hir) = self.pass_reachable_expr(field_expr, ExprState::IsExpr)?;

                                if !self.types_are_same(spec_name.loc(), &spec_field_ty, &field.1)? {
                                    self.add_error(CheckerError::WrongTyForField {
                                        struct_name: struct_name.clone(),
                                        field_name: field.0.clone(),
                                        supplied_ty: spec_field_ty,
                                        expected_ty: field.1.clone(),
                                    })
                                }
                                
                                hir_fields.push(spec_field_hir);
                            } else {
                                self.add_error(CheckerError::FieldNotProvidedWhenInstantiating {
                                    struct_name: struct_name.clone(),
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

    /// Validates a binary expression.
    fn pass_bin_expr(
        &mut self,
        BinaryExpr {
            left_hand_side,
            op,
            right_hand_side,
        }: &BinaryExpr,
    ) -> Option<(Type, HIRExpr)> {
        let (lhs_ty, lhs_hir) = self.pass_reachable_expr(&left_hand_side, ExprState::IsExpr)?;
        let (rhs_ty, rhs_hir) = self.pass_reachable_expr(&right_hand_side, ExprState::IsExpr)?;

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
    ) -> Option<(Type, HIRExpr)> {
        let (base_ty, base_val) = self.pass_reachable_expr(base, ExprState::IsExpr)?;

        let hir_ty = self.pass_ty(base_ty.clone())?;
        // check if we are accessing Struct or *Struct
        let (name, requires_dereferencing, hir_ty) = match &base_ty {
            Type::Pointer { pointee, mutability: _ } => {
                if let Type::NamedType(name) = &**pointee {
                    (name, true, if let HIRType::Pointer { pointee, mutability } = hir_ty {
                        *pointee
                    } else {
                        unreachable!()
                    })
                } else {
                    self.add_error(
                        CheckerError::AccPropOfNonStructTy(dot, base_ty)
                    );
                    return None
                }
            }
            Type::NamedType(name) => (name, false, hir_ty),
            _ => {
                self.add_error(
                    CheckerError::AccPropOfNonStructTy(dot, base_ty)
                );
                return None
            }
        };
        if let Some(Member::Type(actt)) = self.ctx.lookup_member(&name.index()) {
            if let CtxUserType { ty: UserType::Struct { fields }, .. } = &*actt.borrow() {

                if let Some((field_index, (_, field_type))) = fields.iter().enumerate().find(|element| element.1.0.index() == prop.index()) {
                    let expr = HIRExpr::new_access_property(
                        Box::new(base_val),
                        hir_ty,
                        field_index as u32,
                        self.pass_ty(field_type.clone())?,
                        requires_dereferencing,
                    );
                    
                    Some((field_type.clone(), expr))
                } else {
                    self.add_error(
                        CheckerError::NoSuchPropAtStruct(base_ty, prop.clone())
                    );
                    None
                }
                
            } else {
                self.add_error(
                    CheckerError::AccPropOfNonStructTy(dot, base_ty)
                );
                None
            }
        } else {
            self.add_error(
                CheckerError::AccPropOfNonStructTy(dot, base_ty)
            );
            None
        }
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
        let (callee_type, callee_hir) = self.pass_reachable_expr(&callee, ExprState::IsExpr)?;

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
                if let Some(generics) = prototype.generics() {
                    // there ARE generics
                } else {
                    // there aren't any generics
                    for (arg, param) in prototype.arguments().iter().zip(params.iter()) {
                        let (param_ty, param_expr) =
                            self.pass_reachable_expr(param, ExprState::IsExpr)?;
    
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
            self.pass_reachable_expr(&left_hand_side, ExprState::IsAssignmentLhs)?;

        if let Type::Pointer { pointee, mutability: Some(_) } = variable {
            let (type_of_expression, expression_hir) =
                self.pass_reachable_expr(&right_hand_side, ExprState::IsExpr)?;

            if !self.types_are_same(&op.0, &pointee, &type_of_expression)? {
                // assigning wrong type
                self.add_error(CheckerError::AssignWrongTy {
                    slot_ty: *pointee,
                    expr_loc: right_hand_side.loc(),
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
                    }, if let Type::NamedType(t) = &type_of_expression {
                        if let Some(Member::Type(actt)) = self.ctx.lookup_member(&t.index()) {
                            if let CtxUserType { ty: UserType::Struct { .. }, .. } = &*actt.borrow() {
                                Some(self.pass_ty(type_of_expression)?)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    })),
                ))
            }
        } else if let Type::Pointer { pointee: _, mutability: None } = &variable {
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
                self.pass_expr(&expr, ExprState::IsExpr)?;
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
                        aggregate: if let Type::NamedType(t) = &current_return_type {
                            if let Some(Member::Type(actt)) = self.ctx.lookup_member(&t.index()) {
                                if let CtxUserType { ty: UserType::Struct { .. }, .. } = &*actt.borrow() {
                                    Some(self.pass_ty(current_return_type)?)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        } else {
                            None
                        },
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
        if let Some(var) = self.ctx.lookup_variable_mut(name) {
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
    fn get_var(
        &mut self,
        loc: &Loc,
        name: &NameIndex,
        set_init: bool,
        addrof: bool,
    ) -> Option<(Type, HIRExpr, Option<Loc>, bool)> {
        if let Some(var) = self.ctx.lookup_variable_mut(name) {
            let Variable {
                ty,
                init,
                is_argument,
                mutability,
            } = var;

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
                                    if let HIRType::Struct(_) = self.pass_ty(self.ctx.func_ret_ty())? {
                                        index + 1
                                    } else {
                                        index
                                    },
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
                                if let HIRType::Struct(_) = self.pass_ty(self.ctx.func_ret_ty())? {
                                    index + 1
                                } else {
                                    index
                                },
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
                                    if let HIRType::Struct(_) = self.pass_ty(self.ctx.func_ret_ty())? {
                                        index + 1
                                    } else {
                                        index
                                    },
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
                                if let HIRType::Struct(_) = self.pass_ty(self.ctx.func_ret_ty())? {
                                    index + 1
                                } else {
                                    index
                                },
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
                ))
            }
        } else if let Some(Member::Function(func)) = self.ctx.lookup_member(name) {
            let passed_proto = self.pass_proto(func.borrow().proto(), &func);
            let ty = Type::new_function_pointer(func.borrow().proto().clone());
            let name_of_function = func.borrow().full_name(&self.collection);
            Some((ty, HIRExpr::GlobalFunc(name_of_function, passed_proto?), None, true))
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
    LitTooBigForTy(IntLit, Type),
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
    },
    /// This named type was not found
    /// in the current namespace.
    NamedTypeNotFound(Identifier),
    /// Accessing property of non-struct
    /// type.
    AccPropOfNonStructTy(Loc, Type),
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
    },
    /// Dereference non ptr type.
    DerefNonPtrTy(Loc, Type),
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
                                "The name '{}' already exists inside the namespace",
                                collection.unwrap_get(*name),
                            )
                        }
                        AddMemberError::ChildCollision(name, _member) => {
                            format!(
                                "The name '{}' collides with a child namespace of the same name",
                                collection.unwrap_get(*name)
                            )
                        }
                    }
                )
            }
            CE::InvalidExpressionAsStatement(loc, msg) => {
                format!(
                    "{}Error: Invalid use of expression as statement: {}",
                    loc_to_string(loc, collection),
                    msg
                )
            }
            CE::InvalidExpressionAsValue(loc, msg) => {
                format!(
                    "{}Error: Invalid use of expression as value: {}",
                    loc_to_string(loc, collection),
                    msg
                )
            }
            CE::CantTakeAddrOfRvalExpr(loc) => {
                format!(
                    "{}Error: Cannot take address of an rvalue",
                    loc_to_string(loc, collection)
                )
            }
            CE::LitTooBigForTy(lit, ty) => {
                format!(
                    "{}Error: Literal too '{}' too big for type '{}'",
                    loc_to_string(&lit.0, collection),
                    lit.1,
                    ty_to_string(ty, collection)
                )
            }
            CE::MemberNotFound(loc, name) => {
                format!(
                    "{}Error: Member '{}' not found",
                    loc_to_string(loc, collection),
                    collection.unwrap_get(*name)
                )
            }
            CE::BinOnDiffTys(loc, lhs, rhs) => {
                format!(
                    "{}Error: Cannot use binary operator on different types '{}' and '{}'",
                    loc_to_string(loc, collection),
                    ty_to_string(lhs, collection),
                    ty_to_string(rhs, collection),
                )
            }
            CE::CallNonFunc(loc, ty) => {
                format!(
                    "{}Error: Cannot call non-function type '{}'",
                    loc_to_string(loc, collection),
                    ty_to_string(ty, collection)
                )
            }
            CE::FuncGotDiffParamSizeThanInProto { call_at, in_proto, received, type_of_func_is } => {
                format!(
                    "{}Error: The type '{}' specifies '{in_proto}' arguments but '{received}' parameters were given to the call",
                    loc_to_string(call_at, collection),
                    ty_to_string(type_of_func_is, collection)
                )
            }
            CE::WrongParamTy { param, expected, received, expr_loc } => {
                format!(
                    "{}Error: Wrong type for parameter '{}': expected type '{}' but received type '{}'",
                    loc_to_string(expr_loc, collection),
                    collection.unwrap_get(*param),
                    ty_to_string(expected, collection),
                    ty_to_string(received, collection),
                )
            }
            CE::AssignWrongTy { slot_ty, expr_loc, expr_ty } => {
                format!(
                    "{}Error: Cannot assign to an lvalue of type '{}' a value of type '{}'",
                    loc_to_string(expr_loc, collection),
                    ty_to_string(slot_ty, collection),
                    ty_to_string(expr_ty, collection),
                )
            }
            CE::ChangeConst { lvalue_ty, loc } => {
                format!(
                    "{}Error: Cannot assign to constant lvalue reference type '{}'",
                    loc_to_string(loc, collection),
                    ty_to_string(lvalue_ty, collection)
                )
            }
            CE::UndefinedName(name) => {
                format!(
                    "{}Error: Undefined name '{}'",
                    loc_to_string(&name.0, collection),
                    collection.unwrap_get(name.1),
                )
            }
            CE::CantUseBinOpOnTy(loc, op, ty) => {
                format!(
                    "{}Error: Binary operator '{}' cannot be used in instance of type '{}'",
                    loc_to_string(loc, collection),
                    op.to_string(),
                    ty_to_string(ty, collection),
                )
            }
            CE::SlotRedefinition(name) => {
                format!(
                    "{}Error: Can't redefine the named slot '{}'",
                    loc_to_string(&name.0, collection),
                    collection.unwrap_get(name.1),
                )
            }
            CE::CantHaveValuelessSlot(loc, ty) => {
                format!(
                    "{}Error: Cannot use the valueless type '{}' as the type of a slot",
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
                    "{}Error: Everything from now on is unreachable",
                    loc_to_string(loc, collection)
                )
            }
            CE::ReturningDiffTypeThanDecl { at: loc, decl, ret } => {
                format!(
                    "{}Error: Returned type '{}' does not match expected return type '{}' specified in function prototype",
                    loc_to_string(loc, collection),
                    ty_to_string(ret, collection),
                    ty_to_string(decl, collection),
                )
            }
            CE::UsingUnreachableExprAsVal(loc) => {
                format!(
                    "{}Error: Unreachable expression cannot be used as a value",
                    loc_to_string(loc, collection),
                )
            }
            CE::DoesNotRetInAllPathsButMust { loc, expected_ty } => {
                format!(
                    "{}Error: Function declared to return non-valueless type '{}', but a value is not returned in all code paths",
                    loc_to_string(loc, collection),
                    ty_to_string(expected_ty, collection),
                )
            }
            CE::CondIsntBool(loc, cond) => {
                format!(
                    "{}Error: Value of type '{}' was used as a condition but a value of type 'bool' was expected",
                    loc_to_string(loc, collection),
                    ty_to_string(cond, collection)
                )
            }
            CE::ZeroSizedTypeArray(loc, subty) => {
                format!(
                    "{}Error: Valueless type '{}' cannot be used as an element type for sized arrays",
                    loc_to_string(loc, collection),
                    ty_to_string(subty, collection)
                )
            }
            CE::NegativeSizedArray(loc, len) => {
                format!(
                    "{}Error: Negative integer '{}' cannot be used as the size of an array",
                    loc_to_string(loc, collection),
                    len.1
                )
            }
            CE::StructFieldRedefinition { name, field } => {
                format!(
                    "{}Error: Redefinition of field '{}' for struct '{}'",
                    loc_to_string(field.loc(), collection),
                    collection.unwrap_get(field.index()),
                    collection.unwrap_get(name.index()),
                )
            }
            CE::NamedTypeNotFound(ty) => {
                format!(
                    "{}Error: Named type '{}' was not found within the current namespace",
                    loc_to_string(ty.loc(), collection),
                    collection.unwrap_get(ty.index())
                )
            }
            CE::AccPropOfNonStructTy(loc, ty) => {
                format!(
                    "{}Error: Cannot access property of non-struct type '{}'",
                    loc_to_string(loc, collection),
                    ty_to_string(ty, collection),
                )
            }
            CE::NoSuchPropAtStruct(ty, prop) => {
                format!(
                    "{}Error: Struct '{}' doesn't have a property named '{}'",
                    loc_to_string(prop.loc(), collection),
                    ty_to_string(ty, collection),
                    collection.unwrap_get(prop.index()),
                )
            }
            CE::GenericFunctionNotFound(name) => {
                format!(
                    "{}Error: Generic function '{}' was not found",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                )
            }
            CE::InvalidTemplParamLen { name, expected, found } => {
                format!(
                    "{}Error: Generic function '{}' expected {} template arguments but received {}",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                    expected,
                    found,
                )
            }
            CE::InstantiatingNonStructType(ty) => {
                format!(
                    "{}Error: Could not instantiate the type '{}' as it is not a structure",
                    loc_to_string(ty.loc(), collection),
                    collection.unwrap_get(ty.index()),
                )
            }
            CE::WrongFieldNumberForStruct { name, received, needed } => {
                format!(
                    "{}Error: Struct '{}' expected {} fields but received {} during instantiation",
                    loc_to_string(name.loc(), collection),
                    collection.unwrap_get(name.index()),
                    needed,
                    received,
                )
            }
            CE::FieldNotProvidedWhenInstantiating { struct_name, field, ty } => {
                format!(
                    "{}Error: When instantiating the struct '{}' the field '{}' of type '{}' was not provided",
                    loc_to_string(field.loc(), collection),
                    collection.unwrap_get(struct_name.index()),
                    collection.unwrap_get(field.index()),
                    ty_to_string(ty, collection),
                )
            }
            CE::RepeatedFieldInInstantiation { field, provided } => {
                format!(
                    "{}Error: Field '{}' was provided {} times instead of one",
                    loc_to_string(field.loc(), collection),
                    collection.unwrap_get(field.index()),
                    provided,
                )
            }
            CE::WrongTyForField { struct_name, field_name, supplied_ty, expected_ty } => {
                format!(
                    "{}Error: The type '{}' was expected for the field '{}' but '{}' was received when instantiating the struct '{}'",
                    loc_to_string(field_name.loc(), collection),
                    ty_to_string(expected_ty, collection),
                    collection.unwrap_get(field_name.index()),
                    ty_to_string(supplied_ty, collection),
                    collection.unwrap_get(struct_name.index()),
                )
            }
            CE::DerefNonPtrTy(deref_tok, base) => {
                format!(
                    "{}Error: Cannot dereference the non-pointer type '{}'",
                    loc_to_string(deref_tok, collection),
                    ty_to_string(base, collection),
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
        T::Pointer { pointee, mutability } => format!(
            "{}*{}",
            if mutability.is_some() {
                "mut "
            } else {
                ""
            },
            ty_to_string(pointee, collection)
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
                    "{}{prologue}: Accessing uninitialized slot '{}' of type '{}' before assignment",
                    loc_to_string(loc, collection),
                    collection.unwrap_get(*name),
                    ty_to_string(ty, collection),
                )
            }
            WOR::LoopOnlyExecutesOnce(loc) => {
                format!(
                    "{}{prologue}: Loop body only executes once",
                    loc_to_string(loc, collection),
                )
            }
        }).to_string()
    }
}
