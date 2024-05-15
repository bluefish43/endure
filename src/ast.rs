/*!

# The `ast` module

Contains utilities and items related to the
language's abstract syntax tree.

 */

/*

Proposed syntax:

def add(a int, b int) int in
    sum = a + b;
    return sum;
end

print(add(3, 4));

For defining sum types:

sum Result {T, E} = (
    Ok(T),
    Err(E)
)

# These @[...] things are the attributes.
@[noreturn]
def div(lhs int, rhs int) Result{int, string} in
    match rhs with
        0 in
            return Result:Err("Cannot divide by zero");
        end
        default in
            return Result:Ok(lhs / rhs);
        end
    end
    # if lhs == 0 then
    #     return Result:Err("Cannot divide by zero");
    # end
    # return Result:Ok(lhs / rhs);
end

But the first example is the first one going to be implemented.

*/

/// A collection of owned strings.
pub struct Collection {
    strings: Vec<String>,
    set: HashSet<String>,
}

impl Collection {
    /// Creates a new collection.
    pub fn new() -> Self {
        Collection {
            strings: Vec::new(),
            set: HashSet::new(),
        }
    }

    /// Adds a string to the collection
    /// and returns it.
    pub fn add(&mut self, s: String) -> usize {
        if self.set.insert(s.clone()) {
            let index = self.strings.len();
            self.strings.push(s);
            index
        } else {
            self.strings.iter().position(|item| item == &s).unwrap()
        }
    }

    /// Gets a slice to a string within the collection.
    pub fn get(&self, index: usize) -> Option<&str> {
        self.strings.get(index).map(String::as_str)
    }

    pub fn unwrap_get(&self, index: usize) -> &str {
        self.get(index).unwrap()
    }

    /// Returns the length of the collection.
    pub fn len(&self) -> usize {
        self.strings.len()
    }
}

#[derive(new, Debug, Clone, PartialEq, Getters, Default)]
/// The location of something inside
/// of a file.
pub struct Loc {
    /// The file of where it occurred.
    file: NameIndex,
    /// The line of where it occurred.
    line: usize,
    /// The column where it occurred.
    column: usize,
}

#[derive(Debug, Clone)]
/// An identifier - its location and its name index
pub struct Identifier(pub Loc, pub NameIndex);

impl PartialEq for Identifier {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}

impl Identifier {
    pub fn loc(&self) -> &Loc { &self.0 }
    pub fn index(&self) -> NameIndex { self.1 }
}

#[derive(Debug, Clone)]
/// An integer literal.
pub struct IntLit(pub Loc, pub i128);

/// An attribute applied to anything.
pub enum Attribute {
    Function(FunctionAttribute),
    SumType(SumTypeAttribute),
}

#[derive(Debug, Clone)]
/// An attribute which can go
/// in a function.
pub enum FunctionAttribute {
    /// Specifies that the function
    /// does not return.
    NoReturn,
}

/// An attribute which can go
/// in a sum type
pub enum SumTypeAttribute {
    /// Specifies the primitive of which
    /// the flag of the sum type must be.
    Repr(PrimType),
}

#[derive(new)]
/// The declaration of a namespace.
pub struct NamespaceDecl{
    pub namespace_kw: Loc,
    pub name: Identifier,
    pub left_key: Loc,
    pub decls: Vec<Decl>,
    pub right_key: Loc,
}

#[derive(new)]
/// A declaration.
///
/// A function declaration, a sum type
/// declaration or any other of those.
pub enum Decl {
    /// The declaration of a function.
    FunctionDecl(FunctionDecl),
    NamespaceDecl(NamespaceDecl)
}

#[derive(new)]
/// Declaring a function within the
/// local namespace.
pub struct FunctionDecl {
    /// All of the specified attributes to this function.
    pub attrs: Vec<FunctionAttribute>,
    /// The `def` keyword, starting the declaration.
    pub def: Loc,
    /// The prototype of the function.
    pub prototype: Prototype,
    /// The block of the function.
    pub block: Block,
}

#[derive(new, Debug, Clone, Getters)]
/// The prototype of the function, including its signature
/// (ins and outs), name and return type.
pub struct Prototype {
    /// The name of the function which is being declared.
    pub name: Identifier,
    /// The left parenthesis, opening the arguments.
    left_paren: Loc,
    /// The arguments of the function.
    pub arguments: Vec<Argument>,
    /// The right parenthesis, closing the arguments.
    right_paren: Loc,
    /// The return type.
    /// Note: if not provided, this defaults to `void`.
    pub return_type: Box<Type>,
    /// If this function is marked as `unsafe`.
    pub unsafety: bool,
}

#[derive(new, Debug, Clone)]
/// The argument of the function.
pub struct Argument {
    /// The name of the argument.
    pub name: Identifier,
    /// The type of the argument.
    pub ty: Type,
}

#[derive(new, Getters, Debug)]
/// The block of the function.
pub struct Block {
    /// The `in`, `then` or any other
    /// keyword which denotes the start
    /// of the block.
    start: Loc,
    /// The actual block contents.
    stmts: Vec<Expr>,
    /// The `end` keyword.
    end: Loc,
}

pub mod expr {
    /*!

    # The `expr` submodule

    This module contains utilies and enums related
    to working with all available expression types.
    We keep them separate from the other nodes because
    there is a lot of types of expressions.

     */

    use derive_new::new;

    use super::{Block, Identifier, IntLit, Loc, Type};

    #[derive(Debug)]
    /// A while loop.
    pub struct WhileLoop{
        pub while_kw: Loc,
        pub condition: Box<Expr>,
        pub block: Block,
    }

    #[derive(Debug)]
    /// A conditional expression
    pub struct Conditional{
        pub if_kw: Loc,
        pub condition: Box<Expr>,
        pub then: Block,
        pub else_part: Option<(
            Loc,
            Block,
        )>,
    }

    #[derive(Debug)]
    /// An expression which can be used
    /// as a value or not.
    pub enum Expr {
        AsReference(AsReferenceExpr),
        Literal(LiteralExpr),
        Binary(BinaryExpr),
        Assignment(AssignmentExpr),
        SlotDecl(Identifier, Type),
        Call(CallExpr),
        /// The use of a variable as an expression.
        Variable(Identifier),
        Return(ReturnExpr),
        Conditional(Conditional),
        WhileLoop(WhileLoop),
    }

    #[derive(Debug)]
    /// A special type of expression in which,
    /// if available, returns an lvalue instead
    /// of an rvalue.
    ///
    /// For example: wrapping accessing the field
    /// of a struct within `AsReference` returns
    /// the pointer to the field of the struct
    /// instead of the value itself, or in case
    /// of a variable, returns a pointer to its
    /// allocated memory instead of just loading
    /// its value.
    ///
    /// This is very important for supporting taking
    /// the address of a variable (like in `&a`) or
    /// in assignments, where you have the left hand
    /// side of the operator and the right hand side.
    ///
    /// This is also very important for supporting
    /// assignments to all kinds of things.
    pub struct AsReferenceExpr(pub Loc, pub Box<Expr>);

    /// A zero-cost wrapper in a binary expression
    /// where the operator is `=`. This is used to
    /// tell the compiler to handle this binary
    /// expression differently than it would treat
    /// a regular binary expression, where the types
    /// of the left and right hand side have to be the
    /// same, and so on.
    ///
    /// This changes it to these new rules:
    /// * The left hand side must be an lvalue OR must
    ///   support having its reference taken;
    #[repr(transparent)]
    #[derive(Debug)]
    pub struct AssignmentExpr(pub BinaryExpr);

    #[derive(Debug, Clone)]
    /// A literal value: a value which can
    /// be represented as a single token, like
    /// an integer, float, string, boolean or
    /// others.
    ///
    /// Arrays are also included in this.
    pub enum LiteralExpr {
        /// An integer literal.
        Int(IntLit),
    }

    #[derive(Debug)]
    /// A binary expression is formed by the
    /// left hand side (the left side of the
    /// binary operator), the binary operator
    /// (like +, -, *, << and etc.) and the
    /// right hand side (an expression to
    /// the right side of the binary operator).
    pub struct BinaryExpr {
        /// The left hand side of the binary
        /// operator.
        pub left_hand_side: Box<Expr>,

        /// The operator of this expression.
        pub op: (Loc, BinaryOp),

        /// The right hand side of the binary
        /// operator.
        pub right_hand_side: Box<Expr>,
    }

    #[derive(Debug)]
    /// The returning of a value.
    pub struct ReturnExpr {
        pub ret_kw: Loc,
        pub expr: Option<Box<Expr>>,
    }

    #[derive(Debug, Clone)]
    /// A binary operator, like +, - and *.
    pub enum BinaryOp {
        /// The addition operator.
        Plus,
    }

    impl ToString for BinaryOp {
        fn to_string(&self) -> String {
            match self {
                Self::Plus => "+",
            }.to_string()
        }
    }

    #[derive(Debug, new)]
    /// A function call.
    pub struct CallExpr {
        /// What we're calling.
        pub callee: Box<Expr>,
        /// The parameters used in the call..
        pub params: Vec<Expr>,
    }

    impl Expr {
        /// Returns the location of an expression.
        pub fn loc(&self) -> Loc {
            match self {
                Expr::AsReference(asref) => asref.0.clone(),
                Expr::Assignment(assignment) => assignment.0.left_hand_side.loc(),
                Expr::Binary(bin) => bin.left_hand_side.loc(),
                Expr::Call(c) => c.callee.loc(),
                Expr::Literal(lit) => match lit {
                    LiteralExpr::Int(i) => i.0.clone(),
                }
                Expr::Variable(v) => v.0.clone(),
                Expr::SlotDecl(name, _ty) => name.0.clone(),
                Expr::Return(r) => r.ret_kw.clone(),
                Expr::Conditional(Conditional { if_kw, .. }) => if_kw.clone(),
                Expr::WhileLoop(WhileLoop { while_kw, condition, block }) => while_kw.clone(),
            }
        }
    }
}

use std::collections::HashSet;

use derive_getters::Getters;
use derive_new::new;
use typing::*;

use self::expr::Expr;

pub mod typing {
    //! # The `typing` submodule
    //! Utilities related to AST types.

    use derive_new::new;

    use super::{Identifier, IntLit, Loc, Prototype};

    /*

    Proposed primitive types:
    * i8, i16, i32 and i64 -   signed integer types.
    * u8, u16, u32 and u64 - unsigned integer types.
    * f32 and f64          - floating point   types.
    * bool                 - boolean, true or false.

     */

    /// The index of a name within
    /// the set of strings of the AST.
    ///
    /// This is done to use less memory
    /// to represent the AST.
    pub type NameIndex = usize;

    #[derive(Debug, Clone, new, PartialEq)]
    /// A simple, primitive type.
    pub enum PrimType {
        /// One of the unsigned integer types.
        Int(TypeBits),
        /// One of the signed integer types.
        UInt(TypeBits),
        /// One of the floating point types.
        Float(TypeBits),
        /// A boolean value - true or false.
        Bool,
    }

    #[derive(Debug, Clone, PartialEq)]
    /// The bits of a type.
    pub enum TypeBits {
        /// An 8-bit-sized type.
        B8,
        /// A 16-bit-sized type.
        B16,
        /// A 32-bit-sized type.
        B32,
        /// A 64-bit-sized type.
        B64,
    }

    /*

    Proposed types:
    * Primitive types being represented by `PrimType`.
    * Named types (to be found by the semantic analyzer
                   later)
    * Sized arrays of other types (as in [32 of u64])
    * Void     - `void` is like universe, representing
                  no value, except for the fact that it
                  does not necessarily mean an unreachable
                  condition.
    * Universe - `universe` is an internally used type
                  which represents a condition which
                  is never going to occur. Universe can
                  convert in all types that there are.

     */

    #[derive(Debug, Clone, new)]
    /// Any of the supported types.
    pub enum Type {
        /// A primitive type.
        Primitive {
            /// The token which represents the
            /// primitive type.
            loc: Loc,
            /// The primitive type itself.
            ty: PrimType,
        },
        /// A named type.
        NamedType(Identifier),
        /// A sized array as in `[32 of u64]`.
        SizedArray {
            /// The left bracket token.
            left_bracket: Loc,
            /// The size of the array.
            size: IntLit,
            /// The `of` keyword.
            of: Loc,
            /// The element type.
            element_type: Box<Type>,
            /// The right bracket token.
            right_bracket: Loc,
        },
        /// It's essentially a pointer, but we
        /// may add special checkings in the future.
        Pointer(Box<Type>),
        /// A pointer to a function.
        FunctionPointer(Prototype),
        /// The void     type.
        Void,
        /// The universe type.
        Universe,
    }

    impl Type {
        /// Returns if the type is trivially copyable
        /// (primitives or sized arrays of primitives).
        pub fn is_trivially_copyable(&self) -> bool {
            match self {
                Self::Primitive { .. } => true,
                Self::SizedArray { element_type, .. } => {
                    element_type.is_trivially_copyable()
                }
                Self::Void
                | Self::Universe => true,
                _ => false
            }
        }

        pub fn is_float(&self) -> bool {
            matches!(self, Self::Primitive { ty: PrimType::Float(_), .. })
        }

        pub fn is_int(&self) -> bool {
            matches!(self, Self::Primitive { ty: PrimType::Int(_), .. })
        }

        pub fn is_uint(&self) -> bool {
            matches!(self, Self::Primitive { ty: PrimType::UInt(_), .. })
        }
    }

    // TODO: Move this within the context so we can
    //       make sure that types with the same name
    //       but in different namespaces are treated
    //       differently.
    impl PartialEq for Type {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (Self::Universe, _) => true,
                (_, Self::Universe) => true,
                (Self::Primitive { ty, .. }, Self::Primitive { ty: ty2, .. }) => ty == ty2,
                (Self::NamedType(named), Self::NamedType(named2)) => named == named2,
                (Self::Void, Self::Void) => true,
                (Self::Pointer(pointee1), Self::Pointer(pointee2)) => pointee1 == pointee2,
                _ => false,
            }
        }
    }
}
