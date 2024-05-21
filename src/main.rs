use std::process::ExitCode;

use ansi_term::Color;
use ast::{
    expr::{
        AsReferenceExpr, AssignmentExpr, BinaryExpr, BinaryOp, CallExpr, Expr, LiteralExpr,
        ReturnExpr,
    }, generics::{Generic, Generics}, tdecl::{TypeDecl, UserType}, typing::{PrimType, Type, TypeBits}, Argument, Block, Collection, Decl, FunctionDecl, Identifier, IntLit, Loc, NamespaceDecl, Prototype
};
use check::Checker;
use inkwell::{context::Context, targets::CodeModel, OptimizationLevel};

use crate::codegen::{Emmitter, ExportFormat, ExportOptions};

mod ast;
mod check;
mod codegen;

fn main() -> ExitCode {
    let mut collection = Collection::new();
    let set_value_name = collection.add("set_value".to_string());
    let main_name = collection.add("main".to_string());
    let other_func_name = collection.add("other_func".to_string());
    let my_param_name = collection.add("my_param".to_string());
    let my_param2_name = collection.add("my_param2".to_string());
    let my_slot_name = collection.add("my_slot".to_string());
    let my_field_name = collection.add("my_field".to_string());
    let my_field2_name = collection.add("my_field2".to_string());
    let my_namespace_name = collection.add("mynamespace".to_string());
    let my_struct_name = collection.add("MyStruct".to_string());
    let t_name = collection.add("T".to_string());
    let loc = Loc::new(0, 0, 0);
    let global = &[Decl::NamespaceDecl(NamespaceDecl::new(
        loc.clone(),
        Identifier(loc.clone(), my_namespace_name),
        loc.clone(),
        vec![
            Decl::TypeDecl(TypeDecl::new(
                loc.clone(),
                Identifier(
                    loc.clone(),
                    my_struct_name,
                ),
                loc.clone(),
                UserType::Struct {
                    fields: vec![
                        (
                            Identifier(
                                loc.clone(),
                                my_field_name,
                            ),
                            Type::new_primitive(
                                loc.clone(),
                                PrimType::Int(TypeBits::B64),
                            )
                        ),
                        (
                            Identifier(
                                loc.clone(),
                                my_field2_name,
                            ),
                            Type::new_primitive(
                                loc.clone(),
                                PrimType::Int(TypeBits::B64),
                            )
                        )
                    ]
                }
            )),
            Decl::FunctionDecl(FunctionDecl::new(
                vec![],
                loc.clone(),
                Prototype::new(
                    Identifier(loc.clone(), set_value_name),
                    loc.clone(),
                    vec![
                        Argument::new(
                            Identifier(
                                loc.clone(),
                                my_param_name,
                            ),
                            Type::new_pointer(
                                Box::new(Type::new_named_type(Identifier(
                                    loc.clone(),
                                    t_name,
                                ))),
                                None,
                            ),
                            None,
                        ),
                        Argument::new(
                            Identifier(
                                loc.clone(),
                                my_param2_name,
                            ),
                            Type::new_named_type(Identifier(
                                loc.clone(),
                                t_name,
                            )),
                            None,
                        )
                    ],
                    loc.clone(),
                    Some(Generics {
                        lbrac: loc.clone(),
                        generics: vec![
                            Generic {
                                name: Identifier(loc.clone(), t_name),
                            }
                        ],
                        rbrac: loc.clone(),
                    }),
                    Box::new(Type::new_primitive(
                        loc.clone(),
                        PrimType::Int(TypeBits::B64),
                    )),
                    true,
                ),
                Block::new(
                    loc.clone(),
                    vec![
                        Expr::Assignment(AssignmentExpr(BinaryExpr {
                            left_hand_side: Box::new(Expr::AsReference(AsReferenceExpr(
                                loc.clone(),
                                Box::new(Expr::AccessProperty(
                                    Box::new(Expr::Variable(Identifier(loc.clone(), my_param_name))),
                                    loc.clone(),
                                    Identifier(loc.clone(), my_field_name),
                                )),
                            ))),
                            op: (loc.clone(), BinaryOp::Plus),
                            right_hand_side: Box::new(Expr::Literal(LiteralExpr::Int(
                                IntLit(loc.clone(), 420),
                            ))),
                        })),
                        Expr::Return(ReturnExpr {
                            ret_kw: loc.clone(),
                            expr: Some(Box::new(Expr::Literal(LiteralExpr::Int(
                                IntLit(loc.clone(), 0),
                            )))),
                        }),
                    ],
                    loc.clone(),
                ),
            )),
            Decl::FunctionDecl(FunctionDecl::new(
                vec![],
                loc.clone(),
                Prototype::new(
                    Identifier(loc.clone(), main_name),
                    loc.clone(),
                    vec![],
                    loc.clone(),
                    None,
                    // Box::new(Type::new_primitive(
                    //     loc.clone(),
                    //     PrimType::Int(TypeBits::B64),
                    // )),
                    Box::new(Type::new_named_type(
                        Identifier(
                            loc.clone(),
                            my_struct_name,
                        ),
                    )),
                    true,
                ),
                Block::new(
                    loc.clone(),
                    vec![
                        Expr::SlotDecl {
                            mutability: None,
                            name: Identifier(loc.clone(), my_slot_name),
                            ty: Type::new_named_type(Identifier(loc.clone(), my_struct_name)),
                        },
                        Expr::Assignment(AssignmentExpr(BinaryExpr {
                            left_hand_side: Box::new(Expr::AsReference(AsReferenceExpr(
                                loc.clone(),
                                Box::new(Expr::Variable(Identifier(loc.clone(), my_slot_name))),
                            ))),
                            op: (loc.clone(), BinaryOp::Plus),
                            right_hand_side: Box::new(Expr::InstantiateStruct(
                                Identifier(loc.clone(), my_struct_name),
                                vec![
                                    (Identifier(loc.clone(), my_field_name), Expr::Literal(LiteralExpr::Int(
                                        IntLit(loc.clone(), 420),
                                    ))),
                                    (Identifier(loc.clone(), my_field2_name), Expr::Literal(LiteralExpr::Int(
                                        IntLit(loc.clone(), 69),
                                    )))
                                ]
                            ))
                        })),
                        Expr::Return(ReturnExpr {
                            ret_kw: loc.clone(),
                            expr: Some(Box::new(Expr::Variable(Identifier(loc.clone(), my_slot_name)))),
                        }),
                    ],
                    loc.clone(),
                ),
            )),
        ],
        loc.clone(),
    ))];
    let mut checker = Checker::new(collection);
    checker.collect(global);

    let hir_decls = checker.pass_program(global);

    let errors = checker.errors();
    let warnings = checker.warnings();

    for error in errors {
        eprintln!("{}", error.to_string(checker.collection()))
    }
    for warning in warnings {
        eprintln!("{}", warning.to_string(checker.collection(), true))
    }
    if !errors.is_empty() {
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

        let context = Context::create();

        let generator;

        unsafe {
            generator = Box::leak(Box::new(Emmitter::new(&context, "main"))) as *mut Emmitter;
            let reference = generator.as_mut().unwrap();
            reference.emmit_program(&hir_decls.as_slice());
            reference.dump();

            match reference.export(
                &ExportOptions {
                    format: ExportFormat::LLVMIR,
                    output: "./a.out",
                    optimization_level: OptimizationLevel::Default,
                    use_pie: false,
                    code_model: CodeModel::Medium,
                    triple: None,
                }
            ) {
                Ok(_) => {
                    eprintln!(
                        "Compilation {} with {} error{} and {} warning{}",
                        Color::Green.bold().paint("SUCCESS"),
                        errors.len(),
                        if errors.len() == 1 { "" } else { "s" },
                        warnings.len(),
                        if warnings.len() == 1 { "" } else { "s" },
                    );
                },
                Err(err) => {
                    eprintln!(
                        "Compilation {} when exporting: {err}",
                        Color::Red.bold().paint("FAILURE")
                    )
                }
            }

            let _ = Box::from_raw(generator);
        }

        ExitCode::SUCCESS
    }
}
