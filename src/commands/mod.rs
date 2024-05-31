use std::{io::{self, stdout, stderr, stdin, BufWriter, Stderr, Write}, str::Split};

use ansi_term::Color;

use crate::ast::expr::{ExprInfo, ExprInfoData};

type IOError = std::io::Error;

use crossterm::{
    cursor,
    event::{self, Event, KeyCode, KeyEvent},
    execute, terminal,
};

#[macro_export]
macro_rules! purple {
    ($l:expr) => {
        Color::Purple.paint($l)
    }
}

#[macro_export]
macro_rules! blue {
    ($l:expr) => {
        Color::Blue.bold().paint($l)
    }
}

#[macro_export]
macro_rules! green {
    ($l:expr) => {
        Color::Green.paint($l)
    }
}

#[macro_export]
macro_rules! red {
    ($l:expr) => {
        Color::Red.paint($l)
    }
}

pub mod help {
    /*! # The `help` command.
    This has the implementation for the help command.
     */

    use std::io::Stdin;

    use crossterm::event::KeyModifiers;

    use super::*;

    /// Controls the terminal for the helper REPL.
    pub struct TerminalController {
        stdin: Stdin,
        stderr: Stderr,
        line: u16,
        history: Vec<String>,
    }

    impl TerminalController {
        /// Constructs a new `TerminalController`.
        pub fn new() -> Self {
            // terminal::enable_raw_mode().unwrap();
            let mut stderr = stderr();
            // execute!(stderr, terminal::EnterAlternateScreen, cursor::Show).unwrap();
            // execute!(stderr, cursor::MoveTo(0, 0)).unwrap();
            execute!(stderr, terminal::EnableLineWrap).unwrap();

            Self {
                stdin: stdin(),
                stderr,
                line: 0,
                history: Vec::new(),
            }
        }

        /// Adds an entry to the history. 
        pub fn add_history_entry(&mut self, entry: String) {
            self.history.push(entry);
        }

        /// Goes to the next line.
        pub fn go_to_next_line(&mut self) {
            self.line += 1;
            writeln!(self.stderr).unwrap();
        }

        /// Clears the current line
        pub fn clear_line(&mut self) {
            let (columns, _) = terminal::size().unwrap();
            write!(self.stderr, "\r{}", " ".repeat(columns.into())).unwrap();
        }

        /// Reads a line from this terminal controller
        pub fn read_raw_line(
            &mut self,
            header: &str,
            current: &mut String,
        ) -> Result<usize, IOError> {
            let mut history_cursor = 0;

            write!(self.stderr, "{}", header).unwrap();
            self.stdin.read_line(current).unwrap();

            // loop {
            //     if let Event::Key(KeyEvent { code, modifiers, kind, state }) = event::read()? {
            //         match code {
            //             // break on new line
            //             KeyCode::Enter => {
            //                 self.go_to_next_line();
            //                 break;
            //             }
            //             KeyCode::Up => {
            //                 if let Some(entry) = self.history.get(history_cursor) {
            //                     let entry = entry.clone();
            //                     self.clear_line();
            //                     write!(
            //                         self.stderr,
            //                         "{header}"
            //                     ).unwrap();
            //                     write!(self.stderr, "{}", entry.trim_end()).unwrap();
            //                     *current = entry;
            //                     history_cursor += 1;
            //                 }
            //             }
            //             KeyCode::Down => {
            //                 if let Some(entry) = self.history.get(history_cursor) {
            //                     let entry = entry.clone();
            //                     self.clear_line();
            //                     write!(
            //                         self.stderr,
            //                         "{header}"
            //                     ).unwrap();
            //                     write!(self.stderr, "{entry}").unwrap();
            //                     *current = entry;
            //                     history_cursor -= 1;
            //                 }
            //             }
            //             // Ctrl + C
            //             KeyCode::Char('c') if modifiers.contains(KeyModifiers::CONTROL) => {
            //                 eprint!("\r{}? ({}/{})", purple!("Are you sure you want to exit"), red!("y"), green!("N"));
            //                 if let Event::Key(KeyEvent { code: KeyCode::Char('y' | 'Y'), .. }) = event::read()? {
            //                     return Ok(1)
            //                 } else {
            //                     self.clear_line();
            //                     write!(
            //                         self.stderr,
            //                         "\r{header}{current}"
            //                     )?;
            //                     self.flush();
            //                 }
            //             }
            //             KeyCode::Char(c) => {
            //                 current.push(c);
            //                 // write!(self.stderr, "{c}")?;
            //                 history_cursor = 0;
            //                 self.flush();
            //             }
            //             KeyCode::Backspace => {
            //                 current.pop();
            //                 self.clear_line();
            //                 write!(
            //                     self.stderr,
            //                     "\r{header}{current}"
            //                 )?;
            //                 self.flush();
            //             }
            //             _ => {},
            //         }
            //     }
            // }
    
            Ok(0)
        }

        /// A missing something error.
        pub fn missing_error(
            &mut self,
            what_is_missing: &'static str,
            for_: &'static str,
            help: &'static str,
        ) -> Result<(), IOError> {
            write!(
                self.stderr,
                "{}: {what_is_missing} is {missing} for {for_}; try '{help}'",
                Color::Red.bold().paint("Error"),
                missing = red!("missing"),
                help = green!(help),
            )?;
            self.go_to_next_line();
            Ok(())
        }

        /// Gets an argument or gets a missing error.
        pub fn get_argument_or<'a>(
            &mut self,
            from: &mut impl Iterator<Item = &'a str>,
            what_is_missing: &'static str,
            for_: &'static str,
            help: &'static str,
        ) -> Result<Option<&'a str>, IOError> {
            match from.next() {
                Some(element) => {
                    Ok(Some(element.trim()))
                }
                None => {
                    self.missing_error(
                        what_is_missing,
                        for_,
                        help
                    )?;
                    Ok(None)
                }
            }
        }
        
        /// An unknown command error.
        pub fn unknown_command_error(
            &mut self,
            command: &str,
        ) -> Result<(), IOError> {
            write!(
                self.stderr,
                "{}: Command '{command}' did {not} match {anything}; try '{help}'",
                Color::Red.bold().paint("Error"),
                not = red!("not"),
                anything = red!("anything"),
                help = green!("help"),
            )?;
            self.go_to_next_line();
            Ok(())
        }
        
        /// Something is invalid.
        pub fn invalid_something(
            &mut self,
            something: &str,
            invalid_input: &str,
            help_command: &str,
        ) -> Result<(), IOError> {
            write!(
                self.stderr,
                "{}: '{invalid_input}' is an {invalid} {something}; try '{help}'",
                Color::Red.bold().paint("Error"),
                invalid = red!("invalid"),
                help = green!(help_command),
            )?;
            self.go_to_next_line();
            Ok(())
        }

        /// Prints the help for the helper.
        fn help_for_helper(&mut self) -> Result<(), IOError> {
            self.helper_message("")?;
            write!(
                self.stderr,
                "    expr          - Get {information} about an {expression}
        command | cmd - Get information about a compilation command",
                information = blue!("information"),
                expression = blue!("expression"),
            )?;
            self.go_to_next_line();
            Ok(())
        }
        
        /// Prints the help for the helper.
        fn help_for_expr(&mut self) -> Result<(), IOError> {
            self.helper_message("expr")?;
        
            let mut outputs = Vec::new();
            let mut max_size: usize = 0;
            
            for expr in get_available_exprs() {
                let exprs = expr.0;
                let helper = expr.1;
                let s = format!(
                    "    {name}",
                    name = exprs.join(" | ").to_string(),
                );
                max_size = max_size.max(s.len());
                outputs.push((s, helper));
            }
        
            for (s, helper) in outputs {
                write!(
                    self.stderr,
                    "{s}{filler} - {helper}",
                    filler = " ".repeat(max_size - s.len())
                )?;
                self.go_to_next_line()
            }
        
            Ok(())
        }
        
        /// Prints a helper message.
        fn helper_message(&mut self, for_: &'static str) -> Result<(), IOError> {
            write!(
                self.stderr,
                "This is the {helper} window{forwhat}, where {you} can ask {help} about the {language}.",
                helper = blue!("helper"),
                you = blue!("you"),
                help = green!("help"),
                language = blue!("language"),
                forwhat = if !for_.is_empty() {
                    format!(" for {for_}")
                } else {
                    "".to_string()
                }
            )?;
            self.go_to_next_line();
            write!(
                self.stderr,
                "Listing {available} commands:",
                available = green!("available"),
            )?;
            self.go_to_next_line();
            Ok(())
        }
        
        /// Prints information about an expression.
        fn print_expr_info(&mut self, data: &ExprInfoData) -> Result<(), IOError> {
        
            // write name and description
            // first
            
            write!(
                self.stderr,
                "{name}: {}\n{description}: {}\n{illustration}: {}\n{tip}: {}",
                data.formal_name,
                data.description,
                Color::RGB(51, 102, 0).paint(format!("/{}/", data.re_illustration)).to_string().as_str(),
                data.tip,
                name = blue!("Name"),
                description = blue!("Description"),
                illustration = blue!("Illustration"),
                tip = blue!("Tip"),
            )?;
            self.go_to_next_line();
            // write examples
            if !data.examples.is_empty() {
                write!(self.stderr, "{examples} ({number}):", number = data.examples.len(), examples = blue!("Examples"))?;
                self.go_to_next_line();
                for example in data.examples.iter() {
                    write!(self.stderr, "    {example}")?;
                    self.go_to_next_line();
                }
            } else {
                write!(self.stderr, "No {examples} were found for the expression", examples = blue!("examples"))?;
                self.go_to_next_line();
            }
            // write usage notes
            if let Some(notes) = data.usage_notes {
                write!(self.stderr, "{notes} ({number}):", number = notes.len(), notes = blue!("Usage Notes"))?;
                self.go_to_next_line();
                for example in notes.iter() {
                    write!(self.stderr, "    {example}")?;
                    self.go_to_next_line();
                }
            } else {
                write!(self.stderr, "No {usage_notes} were found for the expression", usage_notes = blue!("usage notes"))?;
                self.go_to_next_line();
            }
        
            if let Some(related_expressions) = data.related_expressions.as_ref() {
                write!(self.stderr, "{related_expressions}:", related_expressions = blue!("Related Expressions"))?;
                self.go_to_next_line();
                for related in related_expressions.iter() {
                    write!(self.stderr, "    {related}")?;
                    self.go_to_next_line();
                }
            }
        
            Ok(())
        }
        
        /// Prints all available expressions.
        fn print_available_exprs(handle: &mut Stderr) -> Result<(), IOError> {
            Ok(())
        }

        pub fn flush(&mut self) {
            self.stderr.flush().unwrap();
        }

        pub fn stderr(&mut self) -> &mut Stderr {
            &mut self.stderr
        }
    }

    impl Drop for TerminalController {
        fn drop(&mut self) {
            // execute!(self.stderr, terminal::LeaveAlternateScreen, cursor::Show).unwrap();
            // terminal::disable_raw_mode().unwrap();
        }
    }
    
    /// Executes the help command.
    pub fn help_command() -> Result<(), IOError> {
        let helper = Color::Purple.bold().paint("helper");
        let sign = Color::Cyan.bold().paint(">");
        let header = format!("{helper} {sign} ");

        let mut controller = TerminalController::new();
        
        let mut current_input = String::new();

        loop {
            // read the line
            if controller.read_raw_line(&header, &mut current_input)? == 1 {
                return Ok(());
            }
    
            let mut elements = current_input.split(" ");
    
            // try to get command
            let next_element = elements.next();
            if let Some(command) = next_element {
                let command = command.trim();
    
                if command == "" {
                    controller.missing_error(
                        "name",
                        "command",
                        "help"
                    )?;
                    continue;
                }
    
                match command {
                    "expr" => {
                        if let Some(argument) = controller.get_argument_or(
                            &mut elements,
                            "expression to get information about",
                            "command 'expr'",
                            "expr help",
                        )? {
                            if argument == "help" {
                                controller.help_for_expr()?;
                            } else {
                                match info_for_expr(argument) {
                                    Some(information) => {
                                        controller.print_expr_info(&information)?;
                                    }
                                    None => {
                                        controller.invalid_something(
                                            "expression",
                                            argument,
                                            "expr help",
                                        )?;
                                    }
                                }
                            }
                        }
                    }
                    "command" | "cmd" => {
                    }
                    "help" => {
                        controller.help_for_helper()?;
                    }
                    "quit" => {
                        break;
                    }
                    _ => {
                        controller.unknown_command_error(
                            command,
                        )?;
                    }
                }
            } else {
                controller.missing_error(
                    "name",
                    "command",
                    "help"
                )?;
            }

            controller.add_history_entry(current_input);
            controller.go_to_next_line();
            current_input = String::new();
        }

        Ok(())
    }
    
    /// Gets the available expressions.
    fn get_available_exprs() -> &'static [(&'static [&'static str], &'static str)] {
        &[
            (&["asreference", "asref"], "Gets the address of another expression"),
            (&["literal", "lit"], "Values which are constant and 1-token wide"),
            (&["binary", "bin"], "A binary operation"),
            (&["assignment", "assig"], "Assign a value to an address"),
            (&["accessproperty", "accprop"], "Access a property of something"),
            (&["slotdecl", "slot"], "Declare a slot"),
            (&["let"], "Declare and assign to a slot at the same time"),
            (&["call"], "Call a function"),
            (&["variable", "var"], "Using a variable as an expression"),
            (&["genericinstantiation", "genist"], "Instantiates a generic function"),
            (&["instantiatestruct", "iststruct"], "Instantiates a struct"),
            (&["dereference", "deref"], "Dereferences a pointer"),
            (&["return", "ret"], "Returns something or nothing"),
            (&["conditional", "cond"], "Execute a block conditionally"),
            (&["whileloop", "while"], "Loop based on a condition (while it's true)"),
        ]
    }
    
    /// Gets information about this expression.
    pub fn info_for_expr(expr_ty: &str) -> ExprInfo {
        match expr_ty {
            "asreference"
            | "asref" => ExprInfo::Some(ExprInfoData::new(
                "As reference",
                "Takes the address in memory of another expression",
                &[
                    "&my_variable",
                    "&age",
                    "&notes"
                ],
                Some(
                    &[
                        "The expression given to this must be able to have its address being taken"
                    ]
                ),
                None,
                r#"&($expr)"#,
                "Use this when you want to take the address of something in memory",
            )),
            "literal"
            | "lit" => ExprInfo::Some(ExprInfoData::new(
                "Literal",
                "A simple constant value which can be written as (usually) a single token",
                &[
                    "40",
                    "50.1",
                    "true",
                    "false",
                ],
                Some(
                    &[
                        "All literals, with no exception, are constant"
                    ]
                ),
                None,
                r#"(\d+|\d+\.\d+|(true|false))"#,
                "Use this when you want to use a number or boolean value which is known at compile time",
            )),
            "binary"
            | "bin" => ExprInfo::Some(ExprInfoData::new(
                "Binary operation",
                "Applies a binary operation to a left and right hand side of an expression",
                &[
                    "50 + 94",
                    "13.1 - 0.51",
                    "16 << 2",
                ],
                None,
                None,
                r#"($expr) (+|-|*|/|%|<<|>>) ($expr)"#,
                "Use this when you want to compute a binary operation",
            )),
            "assignment"
            | "assig" => ExprInfo::Some(ExprInfoData::new(
                "Assignment",
                "Assigns the value at the right side of the = to the address at the left side of the equal sign",
                &[
                    "my_variable = 45;"
                ],
                Some(
                    &[
                        "The left hand side of the assignment must be able to have its address being taken"
                    ]
                ),
                Some(
                    &[
                        "let",
                    ]
                ),
                r#"($expr) = ($expr)"#,
                "Use this when you want to assign to a variable",
            )),
            "accessproperty"
            | "accprop" => ExprInfo::Some(ExprInfoData::new(
                "Access property",
                "Accesses a property within an aggregate value or a pointer to one",
                &[
                    "Point { x: 45.0, y: 0.0 }.x",
                    "pointer_to_point.x"
                ],
                Some(
                    &[
                        "Must be used on an aggregate type",
                        "If used in a pointer which is null or dangling may cause a segmentation fault",
                    ]
                ),
                None,
                r#"($expr).($ident)"#,
                "Use this when you want to access the property of an aggregate type (or a pointer to one)",
            )),
            "slotdecl"
            | "slot" => ExprInfo::Some(ExprInfoData::new(
                "Slot declaration",
                "Declares a slot without initializing it",
                &[
                    "slot age: i32;",
                    "slot mut lucky_number: i32;",
                ],
                Some(
                    &[
                        "This only declares the slot, not assigning any value to it",
                        "The value at the slot cannot be read before it is assigned to",
                        "Any slot which is not declared mutable explicitly can only be assigned to once",
                    ]
                ),
                Some(
                    &[
                        "let",
                        "assignment",
                    ]
                ),
                r#"slot (mut)? ($ident): ($type);"#,
                "Use this when you want to declare a slot but don't have an initial value yet",
            )),
            "let" => ExprInfo::Some(ExprInfoData::new(
                "Let",
                "Declares and initializes the slot automatically",
                &[
                    "let age = 13;",
                    "let mut lucky_number: i32 = 7;",
                ],
                Some(
                    &[
                        "This is just an alias for first declaring the slot and then assigning to it",
                    ]
                ),
                Some(
                    &[
                        "slot declaration",
                        "assignment",
                    ]
                ),
                r#"let (mut)? ($ident)(: ($type))? = ($expr);"#,
                "Use this when you want to declare a variable and already have an initial value",
            )),
            "call" => ExprInfo::Some(ExprInfoData::new(
                "Call",
                "Calls a function (or an address)",
                &[
                    "factorial(30)",
                    "clamp(0.0, 3.1, 5.0)",
                    "some_operation()",
                ],
                Some(
                    &[
                        "Call directly or indirectly a function"
                    ]
                ),
                None,
                r#"($expr)\(($expr),)*($expr)?\)"#,
                "Use this when you want to call a function",
            )),
            "variable"
            | "var" => ExprInfo::Some(ExprInfoData::new(
                "Variable",
                "Uses the value stored at the slot with the specified name",
                &[
                    "age",
                    "lucky_number",
                ],
                Some(
                    &[
                        "This loads the value stored at the address of the variable, not taking its address"
                    ]
                ),
                None,
                r#"($ident)"#,
                "Use this when you want to use the value stored at a variable",
            )),
            "genericinstantiation"
            | "genist" => ExprInfo::Some(ExprInfoData::new(
                "Generic instantiation",
                "Instantiates the generic function with the specified template parameters and uses it",
                &[
                    "my_function<i32, i64>"
                ],
                Some(
                    &[
                        "This is usually used to instantiate a generic function",
                    ]
                ),
                None,
                r#"($ident)<(($template),)*($template)?>"#,
                "Use this when you want to instantiate a generic",
            )),
            "instantiatestruct"
            | "iststruct" => ExprInfo::Some(ExprInfoData::new(
                "Instantiate struct",
                "Instantiates a struct with the specified fields",
                &[
                    "Person { age: 45 }"
                ],
                Some(
                    &[
                        "Fields not specified at the declaration of the struct may not be used",
                        "All of the fields specified at the struct declaration must be used",
                    ]
                ),
                None,
                r#"($ident) { (($ident): ($expr),)* }"#,
                "Use this when you want to instantiate a struct",
            )),
            "dereference"
            | "deref" => ExprInfo::Some(ExprInfoData::new(
                "Dereference",
                "Reads the value stored at the pointer",
                &[
                    "*pointer_to_age"
                ],
                Some(
                    &[
                        "Dereferencing a null or dangling pointer may result in a segmentation fault",
                    ]
                ),
                None,
                r#"*($expr)"#,
                "Use this when you want to take the address of something in memory",
            )),
            "return"
            | "ret" => ExprInfo::Some(ExprInfoData::new(
                "Return",
                "Returns a value (or nothing)",
                &[
                    "return;",
                    "return 33;",
                ],
                Some(
                    &[
                        "The return statement value's type (or void if no value) must match the current function's return value",
                        "When returning an aggregate value, the return value is passed through a write only pointer at the first parameter and then the return value is copied to where the caller specified",
                    ]
                ),
                None,
                r#"return( ($expr))?;"#,
                "Use this when you want to return something",
            )),
            "conditional"
            | "cond" => ExprInfo::Some(ExprInfoData::new(
                "As reference expression",
                "Takes the address in memory of another expression",
                &[
                    "if is_odd(3) { my_variable = 33; }",
                    "if is_zero(1) { return 0;  } else { return 1;  }"
                ],
                Some(
                    &[
                        "The condition of the if must be a boolean",
                        "The first block is executed if the first condition is true, otherwise the else block is executed (if any)"
                    ]
                ),
                None,
                r#"if ($expr) { ($expr)* }( else { ($expr)* })?"#,
                "Use this when you want to only run something based on a condition",
            )),
            "whileloop"
            | "while" => ExprInfo::Some(ExprInfoData::new(
                "As reference expression",
                "Takes the address in memory of another expression",
                &[
                    "while alive() { speak(); }"
                ],
                Some(
                    &[
                        "The condition of the loop must be a boolean",
                        "The block is executed while the evaluates to true",
                    ]
                ),
                None,
                r#"while ($expr) { ($expr)* }"#,
                "Use this when you want to run something while the condition is true",
            )),
            _ => ExprInfo::None,
        }
    }
}

pub mod args {
    /*!
    # The `args` module
    Responsible for parsing the input arguments and generating a
    `Tasks` and `Settings` under `Solution`.
     */

    use std::{fmt::Display, num::ParseIntError};

    use crate::codegen::{ExportFormat, ExportOptions, OptimizationOptions};

    use super::*;

    use derive_getters::Getters;
    use inkwell::{targets::CodeModel, OptimizationLevel};
    use utils::*;

    use derive_new::new;

    use ArgumentParsingError as APE;

    // #[derive(new)]
    /// One task to do.
    pub enum Task {
        /// Builds an input file into an output file.
        Build(BuildTask),
        /// Display the help console.
        Help,
    }

    #[derive(new, Getters)]
    pub struct BuildTask {
        /// The input file.
        input_file: String,
    }

    #[derive(new, Getters)]
    /// The configuration for the program.
    pub struct Settings {
        /// The export options to use.
        export_options: ExportOptions,
    }

    #[derive(new, Getters)]
    /// Contains everything related to what we should do.
    pub struct Solution {
        settings: Settings,
        task: Task,
    }

    impl Solution {
        /// Parse the solution from the program arguments.
        pub fn from_args() -> Result<Self, ArgumentParsingError> {
            let mut args = std::env::args();
            // skip program name
            args.next();
            // parse them
            Self::from_iter(args)
        }

        /// Parse the solution from an iterator of strings
        pub fn from_iter(mut iter: impl Iterator<Item = String>) -> Result<Self, ArgumentParsingError> {
            // get subcommand name
            let subcommand_name = require_from_iter(
                &mut iter,
                "name",
                "the subcommand".to_string(),
            )?;

            // parse the main subcommand
            let task = match subcommand_name.as_str() {
                "build"
                | "b" => {
                    let input_file = require_from_iter(
                        &mut iter,
                        "input file name",
                        "the build subcommand".to_string(),
                    )?;
                    Task::Build(BuildTask::new(input_file))
                }
                "help"
                | "h" => {
                    Task::Help
                }
                _ => {
                    return Err(
                        APE::new_invalid_option_for(
                            subcommand_name,
                            "the subcommand name".to_string(),
                            None,
                        )
                    )
                }
            };

            // get default settings
            let mut settings = Settings::new(ExportOptions {
                format: ExportFormat::Object,
                output: "a.out".to_string(),
                optimization_level: OptimizationLevel::Default,
                use_pie: false,
                code_model: CodeModel::Medium,
                triple: None,
                opts: OptimizationOptions::default(),
            });
            
            // parse flags until we can
            while let Some(arg) = iter.next() {
                match arg.as_str() {
                    // export options related
                    "--output"
                    | "--out"
                    | "-o" => {
                        // set output file
                        let output_file = require_from_iter(
                            &mut iter,
                            "output file name",
                            format!("the option '{arg}'"),
                        )?;
                        settings.export_options.output = output_file;
                    }
                    a if a == "--opt-level"
                            || a.starts_with("-O") => {
                        if a == "--opt-level" {
                            // parse next argument as optimization level
                            let optlevel_string = require_from_iter(
                                &mut iter,
                                "optimization level",
                                format!("the option '--opt-level'"),
                            )?;
                            
                            let optlevel = parse_optlevel_from_str(&optlevel_string)?;

                            settings.export_options.optimization_level = optlevel;
                        } else if a.len() == 1 {
                            return Err(APE::new_required_element_not_found(
                                "optimization level".to_string(),
                                "the '-O[0-3]' option".to_string(),
                            ))
                        } else {
                            let optlevel_str = &a[2..];
                            
                            let optlevel = parse_optlevel_from_str(optlevel_str)?;

                            settings.export_options.optimization_level = optlevel;
                        }
                    }
                    "--use-pie"
                    | "--pie" => {
                        settings.export_options.use_pie = true;
                    }
                    option if ["--code-model", "--model", "-M"].contains(&option) => {
                        let code_model_string = require_from_iter(
                            &mut iter,
                            "code model",
                            format!("the option '{option}'")
                        )?;

                        let code_model = parse_codemodel_from_str(&code_model_string)?;

                        settings.export_options.code_model = code_model;
                    }
                    "--triple"
                    | "-t" => {
                        let target_triple = require_from_iter(
                            &mut iter,
                            "target triple",
                            "the option '--triple | -t'".to_string(),
                        )?;
                        settings.export_options.triple = Some(target_triple);
                    }
                    "--export-format"
                    | "--format" => {
                        let export_format_string = require_from_iter(
                            &mut iter,
                            "export format",
                            "the option '--export-format | --format'".to_string(),
                        )?;
                        let format = parse_format_from_str(&export_format_string)?;
                        settings.export_options.format = format;
                    }
                    "-G" => {
                        // generation options
                        let second_command = require_from_iter(
                            &mut iter,
                            "mode",
                            "the option -G".to_string()
                        )?;
                        parse_code_generation_option(
                            &mut iter,
                            &mut settings,
                            &second_command
                        )?;
                    }
                    // did not match
                    _ => {
                        return Err(ArgumentParsingError::new_invalid_option_for(
                            arg,
                            "a flag".to_string(),
                            None,
                        ))
                    }
                }
            }

            // return with okay
            Ok(Solution::new(settings, task))
        }
    }

    mod utils {
        use super::*;

        pub fn require_from_iter(
            iter: &mut impl Iterator<Item = String>,
            what_was_not_found: &'static str,
            for_what: String,
        ) -> Result<String, ArgumentParsingError> {
            match iter.next() {
                Some(element) => Ok(element),
                None => Err(APE::new_required_element_not_found(
                    what_was_not_found.to_string(),
                    for_what,
                ))
            }
        }

        pub fn parse_optlevel_from_str(
            str: &str
        ) -> Result<OptimizationLevel, ArgumentParsingError> {
            Ok(match str.parse::<u8>() {
                Ok(opt_level) => {
                    match opt_level {
                        0 => {
                            OptimizationLevel::None
                        }
                        1 => {
                            OptimizationLevel::Less
                        }
                        2 => {
                            OptimizationLevel::Default
                        }
                        3 => {
                            OptimizationLevel::Aggressive
                        }
                        _ => {
                            return Err(APE::new_invalid_option_for(
                                str.to_string(),
                                "for the optimization level".to_string(),
                                Some("number must be within 0 and 3"),
                            ))
                        }
                    }
                }
                Err(error) => {
                    return Err(APE::new_invalid_number(
                        str.to_string(),
                        error,
                    ))
                }
            })
        }

        pub fn parse_codemodel_from_str(
            str: &str
        ) -> Result<CodeModel, ArgumentParsingError> {
            match str {
                "default"
                | "D" => {
                    Ok(CodeModel::Default)
                }
                "jit-default"
                | "JD" => {
                    Ok(CodeModel::JITDefault)
                }
                "small"
                | "S" => {
                    Ok(CodeModel::Small)
                }
                "kernel"
                | "K" => {
                    Ok(CodeModel::Kernel)
                }
                "medium"
                | "M" => {
                    Ok(CodeModel::Medium)
                }
                "large"
                | "L"
                | "X" => {
                    Ok(CodeModel::Large)
                }
                _ => {
                    Err(APE::new_invalid_option_for(
                        str.to_string(),
                        "for the code model".to_string(),
                        None,
                    ))
                }
            }
        }

        pub fn parse_format_from_str(
            str: &str
        ) -> Result<ExportFormat, ArgumentParsingError> {
            match str {
                "llvm-ir"
                | "ir" => {
                    Ok(ExportFormat::LLVMIR)
                }
                "llvm-bitcode"
                | "bitcode"
                | "bc" => {
                    Ok(ExportFormat::LLVMBitCode)
                }
                "object"
                | "obj"
                | "O" => {
                    Ok(ExportFormat::Object)
                }
                "hir"
                | "H" => {
                    Ok(ExportFormat::HIR)
                }
                "assembly"
                | "asm"
                | "S" => {
                    Ok(ExportFormat::Assembly)
                }
                _ => {
                    Err(APE::new_invalid_option_for(
                        str.to_string(),
                        "for the output format".to_string(),
                        None,
                    ))
                }
            }
        }

        /// Parses a code generation option from the iterator
        /// into the settings. For example: `-G enable c-intrinsic-optimization`
        pub fn parse_code_generation_option(
            iter: &mut impl Iterator<Item = String>,
            options: &mut Settings,
            mode: &str
        ) -> Result<(), ArgumentParsingError> {
            let arg = require_from_iter(
                iter,
                "argument",
                format!("the option -G '{mode}'")
            )?;

            match mode {
                "disable" | "d" => {
                    parse_code_generation_option_impl(
                        options,
                        &arg,
                        false
                    )
                }
                "e" | "enable" => {
                    parse_code_generation_option_impl(
                        options,
                        &arg,
                        true
                    )
                }
                _ => Err(APE::new_invalid_option_for(
                    mode.to_string(),
                    "for the code generation option mode".to_string(),
                    Some("expected either 'd', 'disable', 'e' or 'enable'"),
                ))
            }
        }

        pub fn parse_code_generation_option_impl(
            options: &mut Settings,
            option: &str,
            value: bool
        ) -> Result<(), ArgumentParsingError> {
            match option {
                "c-intrinsic-optimization" => {
                    options.export_options.opts.c_intrinsic_optimization = value;
                }
                _ => {
                    return Err(APE::new_invalid_option_for(
                        option.to_string(),
                        "for the code generation option to change".to_string(),
                        None,
                    ));
                }
            }

            Ok(())
        }
    }

    #[derive(new)]
    /// An error occurred during argument parsing.
    pub enum ArgumentParsingError {
        /// An element which was required was not found.
        RequiredElementNotFound {
            what_was_not_found: String,
            for_what: String,
        },
        /// The input option is invalid for something.
        InvalidOptionFor {
            option: String,
            for_what: String,
            extra_info: Option<&'static str>,
        },
        /// Is not a valid number.
        InvalidNumber(String, ParseIntError),
    }

    impl Display for ArgumentParsingError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                APE::RequiredElementNotFound { what_was_not_found, for_what } => {
                    write!(
                        f,
                        "The {element} was not found for {for_what}",
                        element = red!(what_was_not_found),
                        for_what = red!(for_what),
                    )
                }
                APE::InvalidOptionFor { option, for_what, extra_info } => {
                    write!(
                        f,
                        "The option {option} is invalid for {what}{}",
                        if let Some(info) = extra_info {
                            format!("; {info}")
                        } else { "".to_string() },
                        option = red!(option),
                        what = red!(for_what),
                    )
                }
                APE::InvalidNumber(number, error) => {
                    write!(
                        f,
                        "'{}' is an {invalid} number: {}",
                        number,
                        error,
                        invalid = red!("option"),
                    )
                }
            }
        }
    }
}
