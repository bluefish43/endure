/*!

# The `hir` submodule

This submodule contains utilities related to the
High-Level IR, where we simplify the structure of
the AST to make code generation easier and get rid
of some abstractions that the AST makes.

Some things that HIR does which differ from the
AST are:
* HIR inlines all namespaces names.

 */

#[derive(Debug, new)]
/// A declaration.
///
/// A function declaration, a sum type
/// declaration or any other of those.
pub enum HIRDecl {
    /// The declaration of a function.
    FunctionDecl(HIRFunctionDecl),
}

#[derive(Debug, new)]
/// Declaring a function within the
/// local namespace.
pub struct HIRFunctionDecl {
    /// All of the specified attributes to this function.
    pub attrs: Vec<FunctionAttribute>,
    /// The prototype of the function.
    pub prototype: HIRPrototype,
    /// The block of the function.
    pub block: HIRBlock,
}

#[derive(new, Debug, Clone, Getters)]
/// The prototype of the function, including its signature
/// (ins and outs), name and return type.
pub struct HIRPrototype {
    /// The name of the function which is being declared.
    pub name: HIRIdentifier,
    /// The arguments of the function.
    pub arguments: Vec<HIRArgument>,
    /// The return type.
    /// Note: if not provided, this defaults to `void`.
    pub return_type: Box<HIRType>,
}

#[derive(new, Debug, Clone)]
/// The argument of the function.
pub struct HIRArgument {
    /// The name of the argument.
    pub name: HIRIdentifier,
    /// The type of the argument.
    pub ty: HIRType,
}

#[derive(Debug, new, Getters)]
/// The block of the function.
pub struct HIRBlock {
    /// The actual block contents.
    stmts: Vec<HIRExpr>,
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

    use crate::ast::{expr::{BinaryOp, LiteralExpr}, IntLit, Loc};

    pub type HIRIdentifier = String;

    use super::{HIRBlock, HIRType};

    #[derive(Debug)]
    /// A while loop.
    pub struct HIRWhileLoop{
        pub while_kw: Loc,
        pub condition: Box<HIRExpr>,
        pub block: HIRBlock,
    }

    #[derive(Debug)]
    /// A conditional expression
    pub struct HIRConditional{
        pub if_kw: Loc,
        pub condition: Box<HIRExpr>,
        pub then: HIRBlock,
        pub else_part: Option<(
            Loc,
            HIRBlock,
        )>,
    }

    #[derive(Debug, )]
    /// An expression which can be used
    /// as a value or not.
    pub enum HIRExpr {
        AsReference(HIRAsReferenceExpr),
        Literal(LiteralExpr),
        Binary(HIRBinaryExpr),
        Assignment(HIRAssignmentExpr),
        SlotDecl(HIRIdentifier, HIRType),
        Call(HIRCallExpr),
        /// The use of a variable as an expression.
        Variable(HIRIdentifier),
        /// The use of a global function as a symbol.
        GlobalFunc(HIRIdentifier),
        Return(HIRReturnExpr),
        Conditional(HIRConditional),
        WhileLoop(HIRWhileLoop),
    }

    #[derive(Debug, )]
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
    pub struct HIRAsReferenceExpr(pub Loc, pub Box<HIRExpr>);

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
    #[derive(Debug, )]
    pub struct HIRAssignmentExpr(pub HIRBinaryExpr);

    #[derive(Debug, )]
    /// The type of binary operation.
    pub enum BinOpType {
        /// An integer operation.
        Int,
        /// An unsigned integer operation.
        UInt,
        /// A float operation.
        Float,
    }

    #[derive(Debug, )]
    /// A binary expression is formed by the
    /// left hand side (the left side of the
    /// binary operator), the binary operator
    /// (like +, -, *, << and etc.) and the
    /// right hand side (an expression to
    /// the right side of the binary operator).
    pub struct HIRBinaryExpr {
        /// The left hand side of the binary
        /// operator.
        pub left_hand_side: Box<HIRExpr>,

        /// The operator of this expression.
        pub op: (Loc, BinaryOp),

        /// The right hand side of the binary
        /// operator.
        pub right_hand_side: Box<HIRExpr>,

        /// The type of operation to be applied.
        pub op_ty: BinOpType,
    }

    #[derive(Debug)]
    /// The returning of a value.
    pub struct HIRReturnExpr {
        pub ret_kw: Loc,
        pub expr: Option<Box<HIRExpr>>,
    }

    #[derive(Debug, new)]
    /// A function call.
    pub struct HIRCallExpr {
        /// What we're calling.
        pub callee: Box<HIRExpr>,
        /// The parameters used in the call..
        pub params: Vec<HIRExpr>,
    }
}

use std::collections::HashSet;

use derive_getters::Getters;
use derive_new::new;
use typing::*;

use crate::ast::{FunctionAttribute, Loc};

pub type HIRIdentifier = String;

use self::expr::HIRExpr;

pub mod typing {
    //! # The `typing` submodule
    //! Utilities related to AST types.

    use derive_new::new;

    use crate::ast::{typing::PrimType, IntLit};

    use super::{HIRIdentifier, Loc, HIRPrototype};

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

    #[derive(Debug, Clone, new)]
    /// Any of the supported types.
    /// 
    /// No named types 'cause they're all
    /// inlined now.
    pub enum HIRType {
        /// A primitive type.
        Primitive {
            /// The token which represents the
            /// primitive type.
            loc: Loc,
            /// The primitive type itself.
            ty: PrimType,
        },
        /// A sized array as in `[32 of u64]`.
        SizedArray {
            /// The size of the array.
            size: IntLit,
            /// The element type.
            element_type: Box<HIRType>,
        },
        /// It's essentially a pointer, but we
        /// may add special checkings in the future.
        Pointer(Box<HIRType>),
        /// A pointer to a function.
        FunctionPointer(HIRPrototype),
        /// The void     type.
        Void,
        /// The universe type.
        Universe,
    }

    impl HIRType {
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
    }

    // TODO: Move this within the context so we can
    //       make sure that types with the same name
    //       but in different namespaces are treated
    //       differently.
    impl PartialEq for HIRType {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (Self::Universe, _) => true,
                (_, Self::Universe) => true,
                (Self::Primitive { ty, .. }, Self::Primitive { ty: ty2, .. }) => ty == ty2,
                (Self::Void, Self::Void) => true,
                (Self::Pointer(pointee1), Self::Pointer(pointee2)) => pointee1 == pointee2,
                _ => false,
            }
        }
    }
}

pub type HighLevelIR = HIRDecl;
