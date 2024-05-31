#![allow(dead_code)]

use std::{process::ExitCode, time::Duration};

use ansi_term::Color;
use ast::{
    expr::{
        AsReferenceExpr, AssignmentExpr, BinaryExpr, BinaryOp, CallExpr, Expr, LiteralExpr,
        ReturnExpr,
    }, generics::{Generic, Generics}, matcher::{Case, Pattern, Switch}, tdecl::{Struct, TypeDecl, UserType}, typing::{PrimType, Type, TypeBits}, Argument, Block, Collection, Decl, FunctionDecl, Identifier, IntLit, Loc, NamespaceDecl, Prototype, Receiver
};
use check::Checker;
use codegen::OptimizationOptions;
use commands::args::{Solution, Task};
use either::Either;
use inkwell::{context::Context, targets::CodeModel, OptimizationLevel};

use crate::codegen::{Emmitter, ExportFormat, ExportOptions};

mod ast;
mod check;
mod commands;
mod codegen;

fn report_start() {
    eprintln!();
}

fn report_state(state: &'static str) {
    eprint!("\r{state}");
}

fn report_finish(message: &'static str) {
    eprintln!("\n{message}");
}

macro_rules! tip {
    ($($arg:tt)*) => {{
        eprintln!($($arg)*, tip = blue!("Tip"));
    }};
}

#[tokio::main]
async fn main() -> ExitCode {
    // let solution = match Solution::from_args() {
    //     Ok(solution) => solution,
    //     Err(error) => {
    //         eprintln!(
    //             "{error_str}: {error}",
    //             error_str = red!("Error"),
    //         );
    //         tip!("{tip}: Use the command '{help}'", help = green!("help"));

    //         return ExitCode::FAILURE;
    //     }
    // };

    // match solution.task() {
    //     Task::Help => {
    //         commands::help::help_command().unwrap();
    //     }
    //     Task::Build(_) => {
    //         todo!("Building input file")
    //     }
    // }

    // ExitCode::SUCCESS
    let mut collection = Collection::new();
    let file_name = collection.add("main.ed".to_string());
    let main_name = collection.add("main".to_string());
    let unaligned_field_name = collection.add("unaligned_field".to_string());
    let field_name = collection.add("field".to_string());
    let param_name = collection.add("param".to_string());
    let var_name = collection.add("var".to_string());
    let my_struct_name = collection.add("MyStruct".to_string());
    let my_struct_snake_name = collection.add("my_struct".to_string());
    let my_union_name = collection.add("MyUnion".to_string());
    let get_unaligned_name = collection.add("get_unaligned".to_string());
    let loc = Loc::new(
        file_name,
        1,
        1
    );
    let i64_ty = Type::Primitive {
        loc,
        ty: PrimType::Int(TypeBits::B64)
    };
    let i8_ty = Type::Primitive {
        loc,
        ty: PrimType::Int(TypeBits::B8)
    };
    let my_struct_ty = Type::NamedType(Identifier(loc, my_struct_name));
    let my_union_ty = Type::NamedType(Identifier(loc, my_union_name));

    let global = vec![
        Decl::new_type_decl(TypeDecl::new(
            loc,
            Identifier(loc, my_struct_name),
            loc,
            UserType::Struct(
                Struct::new(
                    vec![
                        (Identifier(loc, unaligned_field_name), i8_ty.clone()),
                        (Identifier(loc, field_name), i64_ty.clone()),
                    ]
                )
            )
        )),
        Decl::new_type_decl(TypeDecl::new(
            loc,
            Identifier(loc, my_union_name),
            loc,
            UserType::Union(
                vec![
                    (Identifier(loc, unaligned_field_name), i8_ty.clone()),
                    (Identifier(loc, field_name), my_struct_ty.clone()),
                ]
            )
        )),
        Decl::new_function_decl(FunctionDecl::new(
            vec![],
            loc,
            Prototype::new(
                Some(Receiver::new(
                    loc,
                    Identifier(loc, my_struct_snake_name),
                    loc,
                    // Box::new(Type::Pointer {
                    //     pointee: Box::new(my_struct_ty.clone()),
                    //     mutability: None,
                    //     lifetime: None,
                    // }),
                    Box::new(my_struct_ty.clone()),
                    loc,
                )),
                Identifier(loc, get_unaligned_name),
                loc,
                vec![],
                loc,
                None,
                // Box::new(Type::Pointer {
                //     pointee: Box::new(
                //         my_union_ty.clone()
                //     ),
                //     mutability: None,
                //     lifetime: None,
                // }),
                Box::new(i8_ty.clone()),
                false
            ),
            Block::new(
                loc,
                vec![
                    Expr::Return(ReturnExpr {
                        ret_kw: loc,
                        expr: Some(Box::new(
                            Expr::AccessProperty(
                                Box::new(Expr::Variable(Identifier(loc, my_struct_snake_name))),
                                loc,
                                Identifier(loc, unaligned_field_name),
                            )
                        ))
                    }),
                ],
                loc
            )
        )),
        // Decl::new_function_decl(FunctionDecl::new(
        //     vec![],
        //     loc,
        //     Prototype::new(
        //         None,
        //         Identifier(loc, main_name),
        //         loc,
        //         vec![
        //         ],
        //         loc,
        //         None,
        //         // Box::new(Type::Pointer {
        //         //     pointee: Box::new(
        //         //         my_union_ty.clone()
        //         //     ),
        //         //     mutability: None,
        //         //     lifetime: None,
        //         // }),
        //         Box::new(i8_ty.clone()),
        //         false
        //     ),
        //     Block::new(
        //         loc,
        //         vec![
        //             Expr::SlotDecl {
        //                 mutability: None,
        //                 name: Identifier(loc, var_name),
        //                 ty: Type::NamedType(Identifier(loc, my_union_name)),
        //             },
        //             Expr::Assignment(AssignmentExpr(BinaryExpr {
        //                 left_hand_side: Box::new(
        //                     Expr::AsReference(AsReferenceExpr(loc, Box::new(
        //                         Expr::Variable(Identifier(loc, var_name))
        //                     )))
        //                 ),
        //                 op: (loc, BinaryOp::Plus),
        //                 right_hand_side: Either::Left(
        //                     Box::new(
        //                         Expr::InstantiateStruct(
        //                             Identifier(loc, my_union_name),
        //                             vec![
        //                                 (Identifier(loc, field_name), Expr::InstantiateStruct(
        //                                     Identifier(loc, my_struct_name),
        //                                     vec![
        //                                         (Identifier(loc, unaligned_field_name), Expr::Literal(LiteralExpr::Int(Type::Primitive {
        //                                             loc,
        //                                             ty: PrimType::Int(TypeBits::B64)
        //                                         }, IntLit(loc, false, 4)))),
        //                                         (Identifier(loc, field_name), Expr::Literal(LiteralExpr::Int(Type::Primitive {
        //                                             loc,
        //                                             ty: PrimType::Int(TypeBits::B64)
        //                                         }, IntLit(loc, false, 300))))
        //                                     ]
        //                                 ))
        //                             ]
        //                         )
        //                     )
        //                 )
        //             })),
        //             Expr::Switch(Switch {
        //                 switch_tok: loc,
        //                 value: Box::new(
        //                     Expr::Variable(Identifier(loc, var_name)),
        //                 ),
        //                 rkey_tok: loc,
        //                 lkey_tok: loc,
        //                 patterns: vec![
        //                     Case::new(
        //                         loc,
        //                         Pattern::DeStructure {
        //                             name: Identifier(loc, my_union_name),
        //                             lkey_tok: loc,
        //                             fields: vec![
        //                                 (
        //                                     None,
        //                                     Identifier(loc, field_name),
        //                                     None,
        //                                 ),
        //                             ],
        //                             ignore: None,
        //                             rkey_tok: loc,
        //                         },
        //                         Block::new(
        //                             loc,
        //                             vec![
        //                                 Expr::Return(ReturnExpr {
        //                                     ret_kw: loc,
        //                                     expr: Some(Box::new(
        //                                         Expr::MethodCall {
        //                                             base: Box::new(
        //                                                 Expr::Variable(
        //                                                     Identifier(loc, field_name)
        //                                                 )
        //                                             ),
        //                                             name: Identifier(loc, get_unaligned_name),
        //                                             params: vec![],
        //                                         }
        //                                     ))
        //                                 })
        //                             ],
        //                             loc,
        //                         ),
        //                     )
        //                 ]
        //             }),
        //             // Expr::Return(ReturnExpr {
        //             //     ret_kw: loc,
        //             //     expr: Some(Box::new(
        //             //         Expr::MethodCall {
        //             //             base: Box::new(
        //             //                 Expr::AccessProperty(
        //             //                     Box::new(Expr::Variable(
        //             //                         Identifier(loc, var_name)
        //             //                     )),
        //             //                     loc,
        //             //                     Identifier(loc, field_name),
        //             //                 )
        //             //             ),
        //             //             name: Identifier(loc, get_unaligned_name),
        //             //             params: vec![],
        //             //         }
        //             //     ))
        //             // })
        //         ],
        //         loc
        //     )
        // )),
        Decl::new_function_decl(FunctionDecl::new(
            vec![],
            loc,
            Prototype::new(
                None,
                Identifier(loc, main_name),
                loc,
                vec![
                ],
                loc,
                None,
                // Box::new(Type::Pointer {
                //     pointee: Box::new(
                //         my_union_ty.clone()
                //     ),
                //     mutability: None,
                //     lifetime: None,
                // }),
                Box::new(i8_ty.clone()),
                false
            ),
            Block::new(
                loc,
                vec![
                    Expr::SlotDecl {
                        mutability: None,
                        name: Identifier(loc, var_name),
                        ty: i8_ty.clone(),
                    },
                    Expr::Assignment(AssignmentExpr(BinaryExpr {
                        left_hand_side: Box::new(
                            Expr::AsReference(AsReferenceExpr(loc, Box::new(
                                Expr::Variable(Identifier(loc, var_name))
                            )))
                        ),
                        op: (loc, BinaryOp::Plus),
                        right_hand_side: Either::Left(
                            Box::new(
                                Expr::Literal(LiteralExpr::Int(Type::Primitive {
                                    loc,
                                    ty: PrimType::Int(TypeBits::B64)
                                }, IntLit(loc, false, 4)))
                            )
                        )
                    })),
                    Expr::Switch(Switch {
                        switch_tok: loc,
                        value: Box::new(
                            Expr::Variable(Identifier(loc, var_name)),
                        ),
                        rkey_tok: loc,
                        lkey_tok: loc,
                        patterns: vec![
                            Case::new(
                                loc,
                                Pattern::Literal(
                                    LiteralExpr::Int(Type::Primitive {
                                        loc,
                                        ty: PrimType::Int(TypeBits::B64)
                                    }, IntLit(loc, false, 5))
                                ),
                                Block::new(
                                    loc,
                                    vec![
                                        Expr::Return(ReturnExpr {
                                            ret_kw: loc,
                                            expr: Some(Box::new(Expr::Literal(
                                                LiteralExpr::Int(Type::Primitive {
                                                    loc,
                                                    ty: PrimType::Int(TypeBits::B64)
                                                }, IntLit(loc, false, 50)))
                                            ))
                                        })
                                    ],
                                    loc,
                                ),
                            ),
                            Case::new(
                                loc,
                                Pattern::Literal(
                                    LiteralExpr::Int(Type::Primitive {
                                        loc,
                                        ty: PrimType::Int(TypeBits::B64)
                                    }, IntLit(loc, false, 3))
                                ),
                                Block::new(
                                    loc,
                                    vec![
                                        Expr::Return(ReturnExpr {
                                            ret_kw: loc,
                                            expr: Some(Box::new(Expr::Literal(
                                                LiteralExpr::Int(Type::Primitive {
                                                    loc,
                                                    ty: PrimType::Int(TypeBits::B64)
                                                }, IntLit(loc, false, 30)))
                                            ))
                                        })
                                    ],
                                    loc,
                                ),
                            ),
                            Case::new(
                                loc,
                                Pattern::WildCard(None, Identifier(loc, field_name)),
                                Block::new(
                                    loc,
                                    vec![
                                        Expr::Return(ReturnExpr {
                                            ret_kw: loc,
                                            expr: Some(Box::new(Expr::Literal(
                                                LiteralExpr::Int(Type::Primitive {
                                                    loc,
                                                    ty: PrimType::Int(TypeBits::B64)
                                                }, IntLit(loc, false, 40)))
                                            ))
                                        })
                                    ],
                                    loc,
                                ),
                            )
                        ]
                    }),
                    // Expr::Return(ReturnExpr {
                    //     ret_kw: loc,
                    //     expr: Some(Box::new(
                    //         Expr::MethodCall {
                    //             base: Box::new(
                    //                 Expr::AccessProperty(
                    //                     Box::new(Expr::Variable(
                    //                         Identifier(loc, var_name)
                    //                     )),
                    //                     loc,
                    //                     Identifier(loc, field_name),
                    //                 )
                    //             ),
                    //             name: Identifier(loc, get_unaligned_name),
                    //             params: vec![],
                    //         }
                    //     ))
                    // })
                ],
                loc
            )
        ))
    ];

    let mut checker = Checker::new(collection);
    checker.collect(&global);

    let hir_decls = checker.pass_program(&global);
    dbg!(&hir_decls);

    let errors = checker.errors();
    let warnings = checker.warnings();

    for error in errors {
        eprintln!("{}", error.to_string(checker.collection()))
    }
    for warning in warnings {
        eprintln!("{}", warning.to_string(checker.collection(), true))
    }
    if !errors.is_empty() {
        
        eprint!("\r");
        // fail if any error occurred
        eprintln!(
            "Compilation {} with {} error{} and {} warning{}",
            Color::Red.bold().paint("FAILED"),
            errors.len(),
            if errors.len() == 1 { "" } else { "s" },
            warnings.len(),
            if warnings.len() == 1 { "" } else { "s" },
        );

        ExitCode::FAILURE
    } else {
        // okay otherwise
        report_state("Generating IR...          ");
        std::thread::sleep(Duration::from_millis(500));

        let context = Context::create();

        let generator;

        unsafe {
            generator = Box::leak(Box::new(Emmitter::new(&context, "main", ExportOptions {
                format: ExportFormat::LLVMIR,
                output: "./a.out".to_string(),
                optimization_level: OptimizationLevel::Default,
                use_pie: false,
                code_model: CodeModel::Medium,
                triple: None,
                opts: OptimizationOptions::default(),
            }))) as *mut Emmitter;
            let reference = generator.as_mut().unwrap();
            reference.emmit_program(&hir_decls.as_slice());

            report_state("Generating output file... ");

            match reference.export() {
                Ok(_) => {
                    eprintln!(
                        "\rCompilation {} with {} error{} and {} warning{}",
                        Color::Green.bold().paint("SUCCESS"),
                        errors.len(),
                        if errors.len() == 1 { "" } else { "s" },
                        warnings.len(),
                        if warnings.len() == 1 { "" } else { "s" },
                    );
                },
                Err(err) => {
                    eprintln!(
                        "\rCompilation {} when exporting: {err}",
                        Color::Red.bold().paint("FAILURE")
                    )
                }
            }

            let _ = Box::from_raw(generator);
        }

        ExitCode::SUCCESS
    }
}
