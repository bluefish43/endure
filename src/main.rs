use std::process::ExitCode;

use ansi_term::Color;
use ast::{expr::{AsReferenceExpr, AssignmentExpr, BinaryExpr, BinaryOp, CallExpr, Expr, LiteralExpr, ReturnExpr}, typing::{PrimType, Type, TypeBits}, Block, Collection, Decl, FunctionDecl, Identifier, IntLit, Loc, NamespaceDecl, Prototype};
use check::Checker;

mod ast;
mod check;
mod codegen;

fn main() -> ExitCode {
    let mut collection = Collection::new();
    let main_name = collection.add("main".to_string());
    let other_func_name = collection.add("other_func".to_string());
    let my_slot_name = collection.add("my_slot".to_string());
    let my_namespace_name = collection.add("mynamespace".to_string());
    let loc = Loc::new(0, 0, 0);
    let global = &[
        Decl::NamespaceDecl(NamespaceDecl::new(
            loc.clone(),
            Identifier(
                loc.clone(),
                my_namespace_name
            ),
            loc.clone(),
            vec![
                // Decl::NamespaceDecl(NamespaceDecl::new(
                //     loc.clone(),
                //     Identifier(
                //         loc.clone(),
                //         my_namespace_name
                //     ),
                //     loc.clone(),
                //     vec![
                    // Decl::FunctionDecl(FunctionDecl::new(
                    //     vec![],
                    //     loc.clone(),
                    //     Prototype::new(
                    //         Identifier(loc.clone(), main_name),
                    //         loc.clone(),
                    //         vec![],
                    //         loc.clone(),
                    //         Box::new(Type::new_primitive(
                    //             loc.clone(),
                    //             PrimType::new_int(TypeBits::B64)
                    //         )),
                    //         false,
                    //     ),
                    //     Block::new(
                    //         loc.clone(),
                    //         vec![
                    //             Expr::SlotDecl(
                    //                 Identifier(loc.clone(), my_slot_name),
                    //                 Type::Primitive {
                    //                     loc: loc.clone(),
                    //                     ty: PrimType::Int(TypeBits::B64),
                    //                 }
                    //             ),
                    //             Expr::Assignment(
                    //                 AssignmentExpr(BinaryExpr {
                    //                     left_hand_side: Box::new(Expr::AsReference(
                    //                         AsReferenceExpr(loc.clone(), Box::new(
                    //                             Expr::Variable(Identifier(loc.clone(), my_slot_name))
                    //                         ))
                    //                     )),
                    //                     op: (loc.clone(), BinaryOp::Plus),
                    //                     right_hand_side: Box::new(Expr::Literal(LiteralExpr::Int(
                    //                         IntLit(loc.clone(), 420)
                    //                     )))
                    //                 })
                    //             ),
                    //             Expr::Call(
                    //                 CallExpr::new(
                    //                     Box::new(
                    //                         Expr::Variable(Identifier(loc.clone(), main_name)),
                    //                     ),
                    //                     vec![]
                    //                 )
                    //             ),
                    //             Expr::Return(ReturnExpr {
                    //                 ret_kw: loc.clone(),
                    //                 expr: Some(Box::new(
                    //                     Expr::Variable(Identifier(loc.clone(), my_slot_name)),
                    //                 )),
                    //             }),
                    //             // Expr::Return(ReturnExpr {
                    //             //     ret_kw: loc.clone(),
                    //             //     expr: None,
                    //             // }),
                    //         ],
                    //         loc.clone(),
                    //     )
                    // ))
                //     ],
                //     loc.clone()
                // )),
                Decl::FunctionDecl(FunctionDecl::new(
                    vec![],
                    loc.clone(),
                    Prototype::new(
                        Identifier(loc.clone(), main_name),
                        loc.clone(),
                        vec![],
                        loc.clone(),
                        Box::new(Type::new_primitive(
                            loc.clone(),
                            PrimType::new_int(TypeBits::B64)
                        )),
                        false,
                    ),
                    Block::new(
                        loc.clone(),
                        vec![
                            Expr::SlotDecl(
                                Identifier(loc.clone(), my_slot_name),
                                Type::Primitive {
                                    loc: loc.clone(),
                                    ty: PrimType::Int(TypeBits::B64),
                                }
                            ),
                            Expr::Assignment(
                                AssignmentExpr(BinaryExpr {
                                    left_hand_side: Box::new(Expr::AsReference(
                                        AsReferenceExpr(loc.clone(), Box::new(
                                            Expr::Variable(Identifier(loc.clone(), my_slot_name))
                                        ))
                                    )),
                                    op: (loc.clone(), BinaryOp::Plus),
                                    right_hand_side: Box::new(Expr::Literal(LiteralExpr::Int(
                                        IntLit(loc.clone(), 420)
                                    )))
                                })
                            ),
                            Expr::Call(
                                CallExpr::new(
                                    Box::new(
                                        Expr::Variable(Identifier(loc.clone(), main_name)),
                                    ),
                                    vec![]
                                )
                            ),
                            Expr::Return(ReturnExpr {
                                ret_kw: loc.clone(),
                                expr: Some(Box::new(
                                    Expr::Variable(Identifier(loc.clone(), my_slot_name)),
                                )),
                            }),
                            // Expr::Return(ReturnExpr {
                            //     ret_kw: loc.clone(),
                            //     expr: None,
                            // }),
                        ],
                        loc.clone(),
                    )
                ))
            ],
            loc.clone()
        )),
    ];
    let mut checker = Checker::new(collection);
    checker.collect(global);

    let hir_decls = checker.pass_program(global);

    let errors = checker.errors();
    let warnings = checker.warnings();

    let report = || {
        for error in errors {
            eprintln!("{}", error.to_string(checker.collection()))
        }
        for warning in warnings {
            eprintln!("{}", warning.to_string(checker.collection(), true))
        }
        eprintln!("{:#?}", hir_decls);
        if !errors.is_empty() {
            // fail if any error occurred
            eprintln!(
                "Compilation {} with {} error{} and {} warning{}",
                Color::Red.bold().paint("FAILED"),
                errors.len(),
                if errors.len() == 1 {
                    ""
                } else {
                    "s"
                },
                warnings.len(),
                if warnings.len() == 1 {
                    ""
                } else {
                    "s"
                },
            );
    
            ExitCode::FAILURE
        } else {
            // okay otherwise
            eprintln!(
                "Compilation {} with {} error{} and {} warning{}",
                Color::Green.bold().paint("SUCCESS"),
                errors.len(),
                if errors.len() == 1 {
                    ""
                } else {
                    "s"
                },
                warnings.len(),
                if warnings.len() == 1 {
                    ""
                } else {
                    "s"
                },
            );
    
            ExitCode::SUCCESS
        }
    };

    report()
}
