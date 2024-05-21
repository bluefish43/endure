/*!

# The `ctx` module

This module contains utilities related to the
management of the type checker context, where we
isolate the context (definitions, variables and
etc.) from the actual type checking to simplify
the implementation and separate concerns.

 */

use std::{cell::RefCell, collections::HashMap, rc::{Rc, Weak}};

use either::Either;

use crate::ast::{
    expr::BinaryOp, tdecl::UserType, typing::{NameIndex, PrimType, Type}, Argument, Collection, FunctionDecl, Identifier, Loc, Prototype
};

use super::{
    namespaces::*, scopes::{Scope, Scopes, Variable}, ActCtxUserType, ActFunction, CheckerError, CtxUserType, Function, GenericFunction, RequiredState
};

const SAFE_SCOPE: bool = false;
const UNSAFE_SCOPE: bool = true;

/// This manages the entire type checking context
/// of the type checker.
pub struct Context {
    /// The root namespaces from which
    /// we begin our search.
    ///
    /// Note: `current_namespaces` can also
    /// be used in the searches, and is the
    /// first one to be searched into.
    root_namespaces: HashMap<NameIndex, ActNamespace>,
    /// The namespace we are currently defining.
    ///
    /// This is implemented as a vector because,
    /// if you don't specify the namespace, it
    /// defaults to `program`, and so like this
    /// we can implement children namespace
    /// scope handling in an easy way.
    ///
    /// This has search priority over
    /// `root_namespaces`.
    current_namespaces: Vec<ActNamespace>,
    /// The current call stack state.
    call_stack: Scopes,
    /// The current function being defined.
    current_function: Option<ActFunction>,
}

impl Context {
    /// Creates a new type checking context.
    pub fn new(collection: &mut Collection) -> Self {
        // create the `program` namespace.
        // it is the first item of `current_namespaces`.

        let program_name = collection.add("program".to_string());
        let program_namespace = Namespace::new(
            // the name of the program
            program_name,
            // we do have no parent here
            None,
        );

        let mut root_namespaces = HashMap::new();
        root_namespaces.insert(program_name, Rc::clone(&program_namespace));

        // return the actual struct
        Self {
            root_namespaces,
            current_namespaces: vec![program_namespace],
            call_stack: Scopes::new(),
            current_function: None,
        }
    }

    pub fn func_ret_ty(&self) -> Type {
        (**self.call_stack.last_function_scope()
            .unwrap()
            .function()
            .as_ref()
            .unwrap()
            .borrow()
            .proto
            .return_type()).clone()
    }

    /// Looks up for a namespace member, according to its name,
    /// in this context.
    ///
    /// It looks into the current namespace only.
    pub fn lookup_member(&self, name: &NameIndex) -> Option<Member> {
        let current_namespace = self.current_namespace();
        search_into_members(current_namespace, name)
    }

    /// Lookups for a variable inside of this context.
    pub fn lookup_variable(&self, name: &NameIndex) -> Option<&Variable> {
        self.call_stack.search_for_variable(name)
    }

    /// Lookups for a variable inside of this context.
    pub fn lookup_variable_mut(&mut self, name: &NameIndex) -> Option<&mut Variable> {
        self.call_stack.search_for_variable_mut(name)
    }

    /// Lookups either a member of a namespace or a variable.
    ///
    /// Note: Variables have high priority in searches.
    pub fn lookup_any(&self, name: &NameIndex) -> Option<SearchItem> {
        if let Some(var) = self
            .lookup_variable(name)
            .map(|var| SearchItem::Variable(var))
        {
            Some(var)
        } else {
            self.lookup_member(name)
                .map(|member| SearchItem::Member(member))
        }
    }

    /// Sets the current function.
    pub fn set_current_function(&mut self, to: ActFunction) {
        self.current_function = Some(to);
    }

    /// Adds a new function scope, having the
    /// current defining function as reference.
    ///
    /// # Panics
    /// This function panics if the current
    /// function is `None`.
    pub fn add_function_scope(&mut self, arguments: &[Argument], unsafety: bool) {
        // push the scope
        self.call_stack.push_scope(
            Some(
                self.current_function
                    .clone()
                    .expect("Adding function scope without having the current function set"),
            ),
            unsafety,
        );

        // add the arguments to last scope
        for (index, argument) in arguments.iter().enumerate() {
            self.insert_variable_in_last_scope(
                argument.name.index(),
                argument.ty.clone(),
                // true because this is an argument
                Some(index),
                argument.mutability.clone(),
                true,
            );
        }
    }

    /// Returns the return type of the current function.
    pub fn current_function_return_type(&self) -> Type {
        for scope in self.call_stack.scopes().iter().rev() {
            if let Some(func) = scope.function() {
                return (**func.borrow().proto.return_type()).clone();
            }
        }
        unreachable!()
    }

    /// Pushes a new non-function scope to the call scope.
    pub fn add_normal_scope(&mut self, safety: bool) {
        self.call_stack.push_scope(None, safety)
    }

    /// Pops a scope from the call stack.
    pub fn pop_scope(&mut self) -> Option<Scope> {
        self.call_stack.pop_scope()
    }

    /// Starts a new root namespace.
    ///
    /// Pushes it to `root_namespaces` and
    /// puts it in the namespaces being
    /// currently defined.
    pub fn start_root_namespace(&mut self, name: NameIndex) {
        let namespace = Namespace::new(name, None);
        self.root_namespaces.insert(name, Rc::clone(&namespace));
        self.current_namespaces.push(namespace)
    }

    /// Starts a new child namespace.
    ///
    /// Adds a new namespace, which will
    /// be a child of the namespace being
    /// currently defined.
    ///
    /// This returns an `Option<ActNamespace>`
    /// which is some if there was already a
    /// namespace with the same name as a child
    /// of the before currently defined namespace.
    ///
    /// The type checker has to handle this.
    pub fn start_child_namespace(&mut self, name: NameIndex) -> Option<ActNamespace> {
        // get the current namespace
        let current_namespace = self.current_namespace();
        let (old_namespace, child_namespace) = add_child_namespace(
            current_namespace,
            name,
            // none here to specify it's empty
            None,
        );
        // push it to the currently being defined pile
        self.current_namespaces.push(child_namespace);
        // return the old namespace
        old_namespace
    }

    /// Starts the specified namespace.
    pub fn start_specified_namespace(&mut self, namespace: ActNamespace) {
        self.current_namespaces.push(namespace);
    }

    /// Instead of creating a new namespace like
    /// `start_child_namespace`, this function instead reputs
    /// an already existing child namespace into the current
    /// namespaces stack.
    pub fn restart_child_namespace(
        &mut self,
        name: NameIndex,
    ) -> Result<ActNamespace, NamespaceSearchError> {
        let namespace = self
            .find_child_of_current_namespace(name)?
            .upgrade()
            .unwrap();

        self.current_namespaces.push(Rc::clone(&namespace));

        Ok(namespace)
    }

    /// Instead of creating a new namespace like
    /// `start_root_namespace`, this function instead reputs
    /// an already existing root namespace into the current
    /// namespaces stack.
    pub fn restart_root_namespace(
        &mut self,
        name: NameIndex,
    ) -> Result<ActNamespace, NamespaceSearchError> {
        let namespace = self.root_namespaces.get(&name).ok_or(vec![name])?;

        self.current_namespaces.push(Rc::clone(&namespace));

        Ok(Rc::clone(&namespace))
    }

    /// Pops a namespace from `current_namespaces`.
    pub fn end_namespace(&mut self) {
        self.current_namespaces.pop();
    }

    /// Searches into the current namespace.
    pub fn find_child_of_current_namespace(
        &mut self,
        name: NameIndex,
    ) -> Result<WeakNamespace, NamespaceSearchError> {
        search_into_children(self.current_namespace(), vec![name])
    }

    /// Inserts a function into the current namespace.
    pub fn insert_function(
        &mut self,
        name: NameIndex,
        prototype: Prototype,
    ) -> Result<Member, AddMemberError> {
        // get current namespace
        let current_namespace = self.current_namespace();
        // downgrade it
        let namespace_used_in_function = Rc::downgrade(current_namespace);

        // add the function
        add_function(
            current_namespace,
            name,
            Function::new(prototype, namespace_used_in_function),
        )
    }

    /// Inserts a generic function into the current namespace.
    pub fn insert_generic_function(
        &mut self,
        name: NameIndex,
        decl: FunctionDecl,
    ) -> Result<Member, AddMemberError> {
        // get current namespace
        let current_namespace = self.current_namespace();
        // downgrade it
        let namespace_used_in_function = Rc::downgrade(current_namespace);

        // add the function
        add_generic_function(
            current_namespace,
            name,
            GenericFunction::new(decl, namespace_used_in_function),
        )
    }

    /// Inserts an user defined tyoe into the current namespace.
    pub fn insert_type(
        &mut self,
        name: NameIndex,
        ty: UserType,
    ) -> Result<Member, AddMemberError> {
        // get current namespace
        let current_namespace = self.current_namespace();
        // downgrade it
        let namespace_used_in_function = Rc::downgrade(current_namespace);

        // add the function
        add_user_type(
            current_namespace,
            name,
            CtxUserType::new(ty, namespace_used_in_function),
        )
    }

    /// Inserts a variable in the last scope, without checking
    /// if it was already defined in previous non-function scopes
    /// (in case of reassignment of a variable for other scope).
    ///
    /// This is not appropriate for variable assignment and should
    /// be used only for function argument insertion, to avoid
    /// doing unnecessary checks.
    pub fn insert_variable_in_last_scope(
        &mut self,
        name: NameIndex,
        ty: Type,
        is_argument: Option<usize>,
        mutability: Option<Loc>,
        is_initialized: bool,
    ) -> Option<Variable> {
        let last_scope = self.call_stack.unwrap_last_scope_mut();
        last_scope.insert_variable(
            name,
            ty,
            // true because this is an argument
            is_argument,
            mutability,
            is_initialized,
        )
    }

    /// Verifies that two types are semantically equal.
    pub fn types_are_equal(
        &self,
        at: &Loc,
        left: &Type,
        right: &Type,
    ) -> Either<bool, Vec<CheckerError>> {
        match (left, right) {
            (Type::NamedType(left_name), Type::NamedType(right_name)) => {
                let mut errors = vec![];
                let left_member = match self.lookup_member(&left_name.index()) {
                    Some(member) => {
                        if let Member::Type(ty) = member {
                            ty
                        } else {
                            errors.push(CheckerError::MemberNotFound(at.clone(), left_name.index()));
                            return Either::Right(errors);
                        }
                    }
                    None => {
                        errors.push(CheckerError::MemberNotFound(at.clone(), left_name.index()));
                        return Either::Right(errors);
                    }
                };
                let right_member = match self.lookup_member(&right_name.index()) {
                    Some(member) => {
                        if let Member::Type(ty) = member {
                            ty
                        } else {
                            errors.push(CheckerError::MemberNotFound(at.clone(), left_name.index()));
                            return Either::Right(errors);
                        }
                    }
                    None => {
                        errors.push(CheckerError::MemberNotFound(at.clone(), right_name.index()));
                        return Either::Right(errors);
                    }
                };
                let borrowed_left = left_member.borrow();
                let borrowed_right = right_member.borrow();
                Either::Left(
                    borrowed_left.ty == borrowed_right.ty
                    && Weak::upgrade(&borrowed_left.parent).unwrap() == Weak::upgrade(&borrowed_right.parent).unwrap()
                )
            }
            _ => Either::Left(left == right),
        }
    }

    /// Returns true if a type supports the input binary operator.
    pub fn type_supports_bin_op(&self, ty: &Type, operator: &BinaryOp) -> bool {
        match ty {
            Type::Primitive { loc: _, ty } => match operator {
                BinaryOp::Plus => {
                    return matches!(
                        ty,
                        PrimType::Int(_) | PrimType::UInt(_) | PrimType::Float(_)
                    )
                }
            },
            _ => false,
        }
    }

    /// Checks if a required state is met.
    pub fn state_is_met(&self, state: RequiredState) -> bool {
        match state {
            RequiredState::UnsafeContext => {
                // verify if at least in one of
                // the stack frames is marked as
                // not safe
                self.call_stack
                    .map_in_function(|scope| *scope.not_safe())
                    .any(|val| val)
            }
        }
    }

    /// Declares a slot in the current scope.
    pub fn declare_slot_in_current_scope(&mut self, name: NameIndex, ty: Type, mutability: Option<Loc>) {
        self.call_stack
            .last_scope_mut()
            .unwrap()
            .insert_variable(name, ty, None, mutability, false);
    }

    /// Gets the current namespace.
    fn current_namespace(&self) -> &ActNamespace {
        let current_namespace = self.current_namespaces.last().unwrap();
        current_namespace
    }
}

/// An item of a search.
///
/// May be a reference to a variable
/// or a member of a namespace.
pub enum SearchItem<'a> {
    /// A variable which was found.
    Variable(&'a Variable),
    /// A member of a namespace.
    Member(Member),
}
