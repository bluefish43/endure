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

#[derive(Debug, new, Clone)]
/// A declaration.
///
/// A function declaration, a sum type
/// declaration or any other of those.
pub enum HIRDecl {
    /// The declaration of a function.
    FunctionDecl(HIRFunctionDecl),
}

#[derive(Debug, new, Clone)]
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

#[derive(Debug, new, Getters, Clone)]
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

    use crate::ast::{
        expr::BinaryOp, IntLit, Loc
    };
    

    pub type HIRIdentifier = String;

    use super::{matcher::HIRSwitch, HIRBlock, HIRDecl, HIRPrototype, HIRType};

    #[derive(Debug, Clone)]
    /// A literal value: a value which can
    /// be represented as a single token, like
    /// an integer, float, string, boolean or
    /// others.
    ///
    /// Arrays are also included in this.
    pub enum HIRLiteralExpr {
        /// An integer literal.
        Int(HIRType, IntLit),
    }

    #[derive(Debug, Clone)]
    /// A while loop.
    pub struct HIRWhileLoop {
        pub while_kw: Loc,
        pub condition: Box<HIRExpr>,
        pub block: HIRBlock,
    }

    #[derive(Debug, Clone)]
    /// A conditional expression
    pub struct HIRConditional {
        pub if_kw: Loc,
        pub condition: Box<HIRExpr>,
        pub then: HIRBlock,
        pub else_part: Option<(Loc, HIRBlock)>,
    }

    #[derive(Debug, new, Clone)]
    /// An expression which can be used
    /// as a value or not.
    pub enum HIRExpr {
        AsReference(HIRAsReferenceExpr),
        Literal(HIRLiteralExpr),
        Binary(HIRBinaryExpr),
        Assignment(HIRAssignmentExpr),
        SlotDecl(HIRIdentifier, HIRType),
        Call(HIRCallExpr),
        /// The use of a variable as an expression.
        Variable(HIRIdentifier, HIRType),
        /// The use of an argument as an expression.
        Argument {
            name: HIRIdentifier,
            ty: HIRType,
            index: usize,
        },
        /// A `switch` statement.
        Switch(HIRSwitch),
        /// Gets the property at the specified index of the
        /// specified structural type at the specified index.
        AccessStructProperty {
            /// The struct expression.
            struct_expr: Box<HIRExpr>,
            /// The struct type.
            struct_ty: HIRType,
            /// The index of the property within the struct.
            property_index: u32,
            /// The type of the property.
            property_ty: HIRType,
            /// If the compiler must load the struct before accessing
            /// its property (in case for a pointer to struct type)
            /// 
            /// Note: As we don't have a special -> operator, we use
            /// this to indicate whether one or another should be used.
            /// 
            /// If we must load it first, it is equivalent to ->, otherwise
            /// it is equivalent to ".".
            must_dereference_first: bool,
        },
        /// Gets the property at the specified index of the specified
        /// union type.
        AccessUnionProperty {
            /// The union expression.
            union_expr: Box<HIRExpr>,
            /// The type of the property.
            property_ty: HIRType,
            /// If the compiler must load the struct before accessing
            /// its property (in case for a pointer to union type)
            /// 
            /// Note: As we don't have a special -> operator, we use
            /// this to indicate whether one or another should be used.
            /// 
            /// If we must load it first, it is equivalent to ->, otherwise
            /// it is equivalent to ".".
            must_dereference_first: bool,
        },
        /// The use of a global function as a symbol.
        ///
        /// Note: we store the prototype here because
        /// we may need to declare it previously as
        /// the order of declaration doesn't matter
        /// in our language.
        GlobalFunc(HIRIdentifier, HIRPrototype),
        Return(HIRReturnExpr),
        Conditional(HIRConditional),
        WhileLoop(HIRWhileLoop),
        /// The instantiation of a struct.
        /// 
        /// We have here the type of the struct and the values of
        /// its fields with options indicating if they are aggregate
        /// or if they are not. If they are, they're memcpy-ed inside
        /// of the struct instead.
        InstantiateStruct(HIRType, Vec<(HIRExpr, Option<HIRType>)>),
        /// The instantiation of a union.
        /// 
        /// We have here the type of the union, the type and the
        /// value of the field we're assigning to and if the
        /// type we're assigning is aggregate or not along with the
        /// type if it is.
        InstantiateUnion(HIRType, Box<HIRExpr>, Option<HIRType>),
        /// Dereferences a pointer.
        Dereference(HIRType, Box<HIRExpr>),

        // -- these aren't really expressions,
        //    but rather helpers

        /// Defines this before evaluating the following expression.
        DefineAndEval(HIRDecl, Box<HIRExpr>),
        /// A sequence of other expressions.
        Sequence(Vec<HIRExpr>),
        /// Executed at the end of the scope.
        Defer(Box<HIRExpr>),
    }

    #[derive(Debug, Clone)]
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
    /// 
    /// This also contains a flag indicating if we're
    /// assigning to an aggregate type or not and if we
    /// are, the aggregate type we're assigning.
    #[derive(Debug, Clone)]
    pub struct HIRAssignmentExpr(pub HIRBinaryExpr, pub Option<HIRType>);

    #[derive(Debug, Clone)]
    /// The type of binary operation.
    pub enum BinOpType {
        /// An integer operation.
        Int,
        /// An unsigned integer operation.
        UInt,
        /// A float operation.
        Float,
    }

    #[derive(Debug, Clone)]
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

    #[derive(Debug, Clone)]
    /// The returning of a value.
    pub struct HIRReturnExpr {
        pub ret_kw: Loc,
        pub expr: Option<Box<HIRExpr>>,
        pub aggregate: Option<HIRType>,
    }

    #[derive(Debug, new, Clone)]
    /// A function call.
    pub struct HIRCallExpr {
        /// What we're calling.
        pub callee: Box<HIRExpr>,
        /// The parameters used in the call..
        pub params: Vec<HIRExpr>,
        /// If this returns an aggregate type.
        pub returns_aggregate: Option<HIRType>,
    }
}

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

    use crate::ast::{typing::{PrimType, TypeBits}, IntLit};

    use super::{HIRPrototype, Loc};

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
        Pointer {
            pointee: Box<HIRType>,
            mutability: Option<Loc>,
        },
        /// A structural type and its fields.
        Struct(Vec<HIRType>),
        /// A sorted struct type (with alignment).
        /// 
        /// For each field, has a flag if it is data
        /// (false) or alignment (true).
        AlignedStruct(Vec<(HIRType, bool)>),
        /// An union type.
        Union(Vec<HIRType>),
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
                Self::SizedArray { element_type, .. } => element_type.is_trivially_copyable(),
                Self::Void | Self::Universe => true,
                _ => false,
            }
        }

        /// Gets the size of this type.
        pub fn size(&self) -> usize {
            match self {
                Self::Primitive { loc, ty } => {
                    ty.size()
                }
                Self::Universe
                | Self::Void => panic!("Obtaining size of illegal type"),
                Self::SizedArray { size, element_type } => {
                    element_type.size() * size.1 as usize
                }
                Self::FunctionPointer(_) => 8,
                Self::Union(u) => {
                    u.iter()
                        .map(|field| field.size())
                        .max()
                        .expect("No fields in union")
                }
                Self::Struct(_) => {
                    panic!("Obtaining size of illegal type (unaligned struct)")
                }
                Self::AlignedStruct(al) => {
                    al.iter()
                        .map(|field| field.0.size())
                        .sum()
                }
                Self::Pointer { pointee, mutability } => std::mem::size_of::<usize>(),
            }
        }

        pub fn is_aggr(&self) -> bool {
            matches!(
                self,
                Self::AlignedStruct(_)
                | Self::Union(_)
            )
        }

        /// Adds proper padding and alignment to this
        /// struct to ensure X-bytes alignment.
        pub fn into_aligned(self, align: usize) -> HIRType {
            if let HIRType::Struct(mut fields) = self {
                let mut aligned_fields = vec![];
                let padding_types = [(8, TypeBits::B64), (4, TypeBits::B32), (2, TypeBits::B16), (1, TypeBits::B8)];

                // Sort fields by size in descending order
                fields.sort_by_key(|f| f.size());

                let mut current_offset = 0;

                for field in fields {
                    let field_size = field.size();

                    // Calculate padding needed for this field's alignment
                    let padding_size = (field_size - (current_offset % field_size)) % field_size;

                    // Add padding using the smallest types
                    let mut remaining_padding = padding_size;
                    for &(size, type_bits) in &padding_types {
                        while remaining_padding >= size {
                            aligned_fields.push((
                                HIRType::Primitive {
                                    loc: Loc::default(),
                                    ty: PrimType::UInt(type_bits),
                                },
                                true,
                            ));
                            remaining_padding -= size;
                            current_offset += size;
                        }
                    }

                    // Add the field
                    aligned_fields.push((field, false));
                    current_offset += field_size;
                }

                // Calculate and add final padding to ensure overall alignment
                let final_padding_size = (align - (current_offset % align)) % align;
                if final_padding_size > 0 {
                    let mut remaining_padding = final_padding_size;
                    for &(size, type_bits) in &padding_types {
                        while remaining_padding >= size {
                            aligned_fields.push((
                                HIRType::Primitive {
                                    loc: Loc::default(),
                                    ty: PrimType::UInt(type_bits),
                                },
                                true,
                            ));
                            remaining_padding -= size;
                        }
                    }
                }

                HIRType::AlignedStruct(aligned_fields)
            } else {
                unreachable!("Called into_aligned() with non-struct type")
            }
        }
    }
}

pub mod matcher {
    /*!
    
    # The `matcher` module

    This module includes everything (or almost everything)
    related to the support of pattern matching within
    endure.

    We here have the switch statement itself, the match arms
    and the patterns.

    */

    use self::expr::HIRLiteralExpr;

    use super::*;

    #[derive(Debug, Clone, Getters, new)]
    /// A `switch` statement.
    pub struct HIRSwitch {
        /// What to switch on.
        value: Box<HIRExpr>,
        /// All of the specified patterns with
        /// their cases.
        patterns: Vec<HIRCase>,
    }

    #[derive(Debug, Clone, Getters, new)]
    /// A single `case` in the `switch`.
    pub struct HIRCase {
        /// The pattern which we are applying.
        pattern: HIRPattern,
        /// The block to be executed if the
        /// pattern matches.
        block: HIRBlock,
    }

    #[derive(Debug, Clone, new)]
    /// A pattern to be matched.
    /// 
    /// TODO:
    /// List patterns, struct destructuring,
    /// guards in case statements
    pub enum HIRPattern {
        /// A literal to be matched.
        Literal(HIRType, HIRLiteralExpr),
        /// An inclusive range between two
        /// integers.
        /// 
        /// Exclusive ranges have already been
        /// inlined to inclusive ranges at
        /// this time.
        Range {
            /// This is the type of the value.
            value_ty: HIRType,
            /// Where this range begins.
            begin: HIRLiteralExpr,
            /// Where this range ends (n - 1).
            end: HIRLiteralExpr,
        },
        /// Destructure a structure with
        /// its fields.
        DeStructure {
            /// The structure we're destructuring.
            structure: HIRType,
            /// If this is an union instead of a struct.
            is_union: bool,
            /// The fields themselves which
            /// were matched, indexes and types.
            /// 
            /// If no pattern is specified then
            /// the pattern is the field name
            /// itself.
            fields: Vec<(String, usize, HIRPattern, HIRType)>,
        },
        /// Matches anything.
        WildCard {
            ty: HIRType,
            is_aggregate: bool,
            name: String
        },
    }
}


pub type HighLevelIR = HIRDecl;
