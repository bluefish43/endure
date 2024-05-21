/*!

# The `scopes` module

Here, we implement algorithms and ways to handle
scope treatment.
This will be used in the type checker context.

 */

use core::slice;

use derive_getters::Getters;
use indexmap::IndexMap;

use crate::ast::{typing::{NameIndex, Type}, Loc};

use super::ActFunction;

/// The type used to store variables in the scope.
///
/// We use `IndexMap` instead of a regular `HashMap`
/// here because their creation order matters when
/// we are invoking type destructors*.
///
/// ***Destructors**: Functions which **run when** a value
/// **exists scope**. This is a concept from **RAII**.
pub type Variables = IndexMap<NameIndex, Variable>;

#[derive(Getters, Clone)]
/// Data about a variable.
pub struct Variable {
    /// The type of the variable.
    ///
    /// As types are not explicitly declared
    /// for locals, this will be always inferred
    /// by the expression it is assigned to.
    pub ty: Type,
    /// If the variable is an argument
    /// or not.
    /// 
    /// Has the index of the argument.
    pub is_argument: Option<usize>,
    /// If the variable was already initialized.
    /// Accessing an uninitialized slot is an error.
    pub init: bool,
    /// If this variable is mutable or not.
    pub mutability: Option<Loc>,
}

impl Variable {
    /// Sets this variable to be initialized.
    pub fn initialize(&mut self) {
        self.init = true;
    }
}

#[derive(Getters)]
/// One single scope, or call frame.
pub struct Scope {
    /// The local variables of the scope.
    variables: Variables,
    /// If this scope is from a function,
    /// and if yes, the function itself.
    ///
    /// We do not include a separate parent
    /// namespace here because the function
    /// already includes it.
    function: Option<ActFunction>,
    /// If this scope is explicitly marked
    /// as `unsafe`, allowing for explicitly
    /// unsafe operations.
    not_safe: bool,
}

impl Scope {
    /// Constructs a new `Scope`.
    pub fn new(function: Option<ActFunction>, not_safe: bool) -> Scope {
        Scope {
            variables: Variables::new(),
            function,
            not_safe,
        }
    }

    /// Searches for a variable in the scope.
    pub fn search_for_variable(&self, variable: &NameIndex) -> Option<&Variable> {
        self.variables.get(variable)
    }

    /// Searches for a variable in the scope.
    pub fn search_for_variable_mut(&mut self, variable: &NameIndex) -> Option<&mut Variable> {
        self.variables.get_mut(variable)
    }

    /// Inserts a variable inside of this scope.
    pub fn insert_variable(
        &mut self,
        name: NameIndex,
        ty: Type,
        is_argument: Option<usize>,
        mutability: Option<Loc>,
        is_initialized: bool,
    ) -> Option<Variable> {
        self.variables.insert(
            name,
            Variable {
                ty,
                is_argument,
                init: is_initialized,
                mutability,
            },
        )
    }
}

#[derive(Getters)]
/// Manages all scopes of the program.
pub struct Scopes {
    /// The list of scopes.
    scopes: Vec<Scope>,
}

impl Scopes {
    /// Constructs a new `Scopes`.
    pub fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    /// Pushes a new scope to these scopes.
    pub fn push_scope(&mut self, function: Option<ActFunction>, not_safe: bool) {
        self.scopes.push(Scope::new(function, not_safe))
    }

    /// Returns an optional shared reference to the last
    /// scope of this `Scopes`.
    pub fn last_scope(&self) -> Option<&Scope> {
        self.scopes.last()
    }

    /// Returns an optional shared reference to the last
    /// scope of this `Scopes` which is the root of a function.
    pub fn last_function_scope(&self) -> Option<&Scope> {
        self.scopes.iter()
            .find(|item| item.function.is_some())
    }

    /// Returns an optional mutable reference to the last
    /// scope of this `Scopes`.
    pub fn last_scope_mut(&mut self) -> Option<&mut Scope> {
        self.scopes.last_mut()
    }

    /// Returns a shared reference to the last
    /// scope of this `Scopes`.
    ///
    /// # Panics
    /// This calls `unwrap` so, if there is
    /// no last scope, this panics.
    pub fn unwrap_last_scope(&self) -> &Scope {
        self.last_scope().unwrap()
    }

    /// Returns a mutable reference to the last
    /// scope of this `Scopes`.
    ///
    /// # Panics
    /// This calls `unwrap` so, if there is
    /// no last scope, this panics.
    pub fn unwrap_last_scope_mut(&mut self) -> &mut Scope {
        self.last_scope_mut().unwrap()
    }

    /// Pops a scope from these scopes.
    pub fn pop_scope(&mut self) -> Option<Scope> {
        self.scopes.pop()
    }

    /// Searches for a variable inside of the scopes.
    pub fn search_for_variable(&self, name: &NameIndex) -> Option<&Variable> {
        // search into all frames for the variable
        for scope in self.scopes.iter().rev() {
            match scope.search_for_variable(name) {
                // return the variable if found
                Some(var) => return Some(var),
                None if scope.function.is_some() => {
                    // if the current scope is a function,
                    // stop the search
                    break;
                }
                None => {
                    // continue otherwise
                    continue;
                }
            }
        }

        // return none if not found
        None
    }

    /// Searches for a variable inside of the scopes.
    pub fn search_for_variable_mut(&mut self, name: &NameIndex) -> Option<&mut Variable> {
        // search into all frames for the variable
        for scope in self.scopes.iter_mut().rev() {
            let is_function_scope = scope.function.is_some();
            match scope.search_for_variable_mut(name) {
                // return the variable if found
                Some(var) => return Some(var),
                None if is_function_scope => {
                    // if the current scope is a function,
                    // stop the search
                    break;
                }
                None => {
                    // continue otherwise
                    continue;
                }
            }
        }

        // return none if not found
        None
    }

    /// Applies a map to all scopes while they are in function.
    pub fn map_in_function<P, O>(&self, pred: P) -> std::vec::IntoIter<O>
    where
        P: FnOnce(&Scope) -> O + Copy,
    {
        let mut output = vec![];
        let mut function_occurred = false;
        for scope in self.scopes.iter().rev() {
            if function_occurred {
                break;
            } else if scope.function.is_some() {
                function_occurred = true;
            }

            output.push(pred(scope));
        }
        output.into_iter()
    }
}
