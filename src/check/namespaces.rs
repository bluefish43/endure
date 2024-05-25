//! # The `namespaces` submodule
//! Utilities related to namespaces and
//! their resolution.
//!
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::ast::{tdecl::UserType, typing::NameIndex, Collection};

use super::{ActCtxUserType, ActFunction, ActGenericFunction, CtxUserType};

/// The children of an already existing namespace.
pub type NamespaceChildren = HashMap<NameIndex, ActNamespace>;

/// Namespaces which we used to this namespace.
pub type UsedNamespaces = HashMap<NameIndex, WeakNamespace>;

/// A single namespace
pub struct Namespace {
    /// The name of this namespace.
    name: NameIndex,
    /// The parent of this namespace.
    parent: Option<Rc<RefCell<Namespace>>>,
    /// The child of this namespace.
    children: HashMap<NameIndex, ActNamespace>,
    /// Used namespaces. We use weak for this
    /// so we don't create cyclic references.
    used: HashMap<NameIndex, WeakNamespace>,

    /// The members of the namespace.
    members: Members,
}

impl PartialEq for Namespace {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
        && self.parent == other.parent
        && self.children == other.children
    }
}

/// A namespace which you can actually use.
pub type ActNamespace = Rc<RefCell<Namespace>>;

/// Used in types which are inside of the
/// namespaces so you can access their parent
/// without causing permanent cyclic references.
pub type WeakNamespace = Weak<RefCell<Namespace>>;

impl Namespace {
    /// Creates a new `ActNamespace`
    /// based on its parent.
    pub fn new(name: NameIndex, parent: Option<Rc<RefCell<Namespace>>>) -> ActNamespace {
        Rc::new(RefCell::new(Self {
            name,
            parent,
            children: NamespaceChildren::new(),
            members: Members::new(),
            used: UsedNamespaces::new(),
        }))
    }
}

/// The members of a namespace.
pub type Members = HashMap<NameIndex, Member>;

#[derive(Debug, Clone)]
/// A member of a namespace which isn't actually a namespace.
///
/// These are mostly functions, but can also be types and so on.
pub enum Member {
    /// A function inside of the namespace.
    Function(ActFunction),
    /// A generic function.
    GenericFunction(ActGenericFunction),
    /// A defined type.
    Type(ActCtxUserType),
}

/// Adds a child namespace to an
/// already existing namespace.
///
/// Returns an `Option<ActNamespace>`
/// for the namespace which was already
/// here (if there was any) at the entry
/// and an `ActNamespace` for the currently
/// inserted namespace.
pub fn add_child_namespace(
    namespace: &ActNamespace,
    name: NameIndex,
    child: Option<ActNamespace>,
) -> (Option<ActNamespace>, ActNamespace) {
    // get the child node to add
    let child_namespace = child.unwrap_or(Namespace::new(name, Some(Rc::clone(namespace))));

    // insert the child namespace and
    // return it
    (
        namespace
            .borrow_mut()
            .children
            .insert(name, Rc::clone(&child_namespace)),
        child_namespace,
    )
}

/// Adds an used namespace to an
/// already existing namespace.
///
/// Returns an `Option<WeakNamespace>`
/// for the namespace which was already
/// here (if there was any) at the entry
/// and an `WeakNamespace` for the currently
/// inserted namespace.
fn add_used_namespace(
    namespace: &ActNamespace,
    name: NameIndex,
    used: WeakNamespace,
) -> (Option<WeakNamespace>, WeakNamespace) {
    // insert the used namespace and
    // return it
    (
        namespace.borrow_mut().used.insert(name, Weak::clone(&used)),
        used,
    )
}

/// A vector for searching inside a namespace.
///
/// As this is a vector, it must be layed out
/// in such a way that the paths searched first
/// are closer to the last element and the first
/// element of the vector is the last to be
/// searched.
pub type NamespaceSearchPath = Vec<NameIndex>;

/// An error when searching for namespaces
/// inside a parent namespace.
///
/// The last indicates where the search failed
/// and the rest are the ones which were found.
///
/// For example: if the list is `vec!["System",
/// "Console", "Writeln"]`, that indicates that
/// `"System"` is where the search started at,
/// `"Console"` was found but `"Writeln"` was not found.
pub type NamespaceSearchError = Vec<NameIndex>;

/// Searches for a namespace search path
/// inside of the namespace, returning the
/// `WeakNamespace` if found or an error
/// if not.
///
/// We use `WeakNamespace` instead of `ActNamespace`
/// here because we may get an used namespace instead
/// of an actual child namespace.
///
/// If we get an used one, we just return it. Othewise,
/// if we
///
/// See [`NamespaceSearchError`] to interpret
/// this function's errors.
pub fn search_into_children(
    namespace: &ActNamespace,
    mut path: NamespaceSearchPath,
) -> Result<WeakNamespace, NamespaceSearchError> {
    let root_name = namespace.borrow().name;
    search_into_children_imp(&Rc::downgrade(namespace), &mut path, vec![root_name])
}

fn search_into_children_imp(
    namespace: &WeakNamespace,
    path: &mut NamespaceSearchPath,
    mut unwound: NamespaceSearchError,
) -> Result<WeakNamespace, NamespaceSearchError> {
    match path.pop() {
        Some(namespace_to_search_for) => {
            // add to unwound
            unwound.push(namespace_to_search_for);

            let upgraded = namespace
                .upgrade()
                .expect("Namespace somehow got out of scope (bug)");
            let mut borrowed = upgraded.borrow_mut();

            // search into children
            match borrowed.children.get_mut(&namespace_to_search_for) {
                Some(child_found) => {
                    search_into_children_imp(&Rc::downgrade(child_found), path, unwound)
                }
                // if not found search into used namespaces
                None => match borrowed.used.get_mut(&namespace_to_search_for) {
                    Some(used_found) => search_into_children_imp(used_found, path, unwound),
                    // if not found is an error
                    None => Err(unwound),
                },
            }
        }
        None => {
            // if there is nothing more to search,
            // then the target namespace is the one
            // we're looking for

            Ok(Weak::clone(namespace))
        }
    }
}

/// Searches inside of a namespace for
/// its members.
pub fn search_into_members<'a>(namespace: &'a ActNamespace, name: &NameIndex) -> Option<Member> {
    let borrowed = namespace.borrow();

    borrowed.members.get(name).cloned()
}

/// Gets the full name of a namespace.
pub fn full_name(namespace: &ActNamespace, collection: &Collection) -> String {
    let mut out = String::new();
    full_name_imp(namespace, collection, &mut out);
    out
}

fn full_name_imp(namespace: &ActNamespace, collection: &Collection, into: &mut String) {
    let borrowed_self = namespace.borrow();
    if let Some(parent) = borrowed_self.parent.as_ref() {
        // add parent string
        full_name_imp(parent, collection, into);
        // add accessor
        into.push('.');
        // add self
        into.push_str(
            collection
                .get(borrowed_self.name)
                .expect("Invalid string index given to namespace"),
        )
    } else {
        into.push_str(
            collection
                .get(borrowed_self.name)
                .expect("Invalid string index given to parent of namespace"),
        );
    }
}

#[derive(Debug)]
/// An error when adding a member
/// to a namespace.
pub enum AddMemberError {
    /// The member already exists within
    /// this namespace.
    ///
    /// Is the index of the name of the
    /// member and the old member.
    AlreadyExists(NameIndex, Member),
    /// The member collides with a child
    /// namespace of the same name.
    ///
    /// Is the index of the name of the
    /// member and the member you were
    /// trying to add.
    ChildCollision(NameIndex, Member),
}

/// Adds a member to a namespace.
pub fn add_member(
    namespace: &ActNamespace,
    name: NameIndex,
    member: Member,
) -> Result<Member, AddMemberError> {
    let mut namespace_ref = namespace.borrow_mut();

    if namespace_ref.children.get(&name).is_some() {
        Err(AddMemberError::ChildCollision(name, member))
    } else {
        match namespace_ref.members.insert(name, member.clone()) {
            Some(old) => Err(AddMemberError::AlreadyExists(name, old)),
            None => Ok(member),
        }
    }
}

/// Adds a function to a namespace.
pub fn add_function(
    namespace: &ActNamespace,
    name: NameIndex,
    function: ActFunction,
) -> Result<Member, AddMemberError> {
    add_member(namespace, name, Member::Function(function))
}

/// Adds a generic function to a namespace.
pub fn add_generic_function(
    namespace: &ActNamespace,
    name: NameIndex,
    function: ActGenericFunction,
) -> Result<Member, AddMemberError> {
    add_member(namespace, name, Member::GenericFunction(function))
}

/// Adds an user defined type to a namespace.
pub fn add_user_type(
    namespace: &ActNamespace,
    name: NameIndex,
    ty: CtxUserType,
) -> Result<Member, AddMemberError> {
    add_member(namespace, name, Member::Type(ActCtxUserType::new(RefCell::new(ty))))
}

#[cfg(test)]
/// Testing for namespace utilities.
mod tests {
    use super::*;

    #[test]
    /// Tests searching into namespaces and
    /// setting them to string.
    fn test_namespace_search_and_to_string() {
        let mut collection = Collection::new();
        let system_name = collection.add("System".to_string());
        let console_name = collection.add("Console".to_string());
        let write_line_name = collection.add("WriteLine".to_string());
        let something_else_name = collection.add("SomethingElse".to_string());
        let mut system = Namespace::new(system_name, None);
        let (_, console) = add_child_namespace(&mut system, console_name, None);
        // testing namespace searching below
        let find_path = vec![something_else_name, write_line_name, console_name];
        match search_into_children(&system, find_path) {
            Err(err) => {
                assert_eq!(
                    err,
                    vec![system_name, console_name, write_line_name],
                    "Output vector of search path failure is incorrect"
                );
            }
            Ok(_) => unreachable!(),
        }

        // check for full name validity
        assert_eq!(
            full_name(&console, &collection),
            "System.Console".to_string()
        );
    }
}
