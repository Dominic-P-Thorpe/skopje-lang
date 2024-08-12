//! Translates an AST of Skopje code to C code which is then written to a file.
//! 
//! The struct [`Transpiler`] is used to translate the AST passed to it when it is instantiated into
//! C which is then written to the passed file. Reasonable effort has been made to ensure the 
//! resulting C code is readable.
//! 
//! In future, it will likely become necessary to package the resulting file of code along with a
//! makefile or other build system so that other files of source code can be included along with any
//! other libraries needed, including a garbage collector and/or arena allocator. Heirarchical
//! arena memory allocation is likely to be used.
//! 
//! # Examples
//! 
//! ```
//! fn main() {
//!     let scanner = Scanner::new("my_file.skj").unwrap();
//!     let mut parser = Parser::new(scanner.tokens);
//!     let ast = parser.parse().unwrap();
//!     let mut transpiler = Transpiler::new(ast, "out.c");
//! }
//! ``` 
use rand::distributions::{Alphanumeric, DistString};
use std::error::Error;
use std::fs::{File, OpenOptions};
use std::io::Write;

use crate::{SyntaxNode, SyntaxTree};


/// The core of the transpiler module, containing data and methods needed to transpile from Skopje
/// to C code.
pub struct Transpiler {
    /// The target file to write the C code to
    file: File,
    // Extra functions which also need to be written to the file at the end of processing
    functions_source: Vec<String>,
    // Used to name auxilliary functions created by the compiler, not the programmer
    auxilliary_func_index: usize,
    /// The AST to be translated into C
    ast: SyntaxTree
}


impl Transpiler {
    /// Creates a new instance of [`Transpiler`] which can be used to write the C translation of the
    /// given AST into the given directory.
    /// 
    /// The directory is created if it does not already exist, and is overwritten if it does.
    /// 
    /// # Example
    /// 
    /// ```
    /// let scanner = Scanner::new("my_file.skj").unwrap();
    /// let mut parser = Parser::new(scanner.tokens);
    /// let ast = parser.parse().unwrap();
    /// let mut transpiler = Transpiler::new(ast, "out.c");
    /// ```
    pub fn new(source: SyntaxTree, target: &str) -> Self {
        Transpiler { 
            file: OpenOptions::new().create(true).truncate(true).write(true).open(target).unwrap(), 
            functions_source: vec![],
            auxilliary_func_index: 0,
            ast: source 
        }
    }


    /// Generates the name of the next compiler-generated auxilliary function and increments
    /// `self.auxilliary_func_index`.
    /// 
    /// The name returned is of the format `_F_<index>__<random_string>` where `index` is the 
    /// current auxilliary function index as a hexadecimal number padded to 8 digits, and 
    /// `random_string` is a randomly generated sequence of 16 alphanumeric or '_' characters
    /// appended to the end.
    /// 
    /// # Example
    /// 
    /// ```
    /// let transpiler: Transpiler = Transpiler::new(syntax_tree, "my_file.cpp");
    /// println!("{}", transpiler.get_next_auxilliary_func_name());
    /// ```
    fn get_next_auxilliary_func_name(&mut self) -> String {
        let id_num: usize = self.auxilliary_func_index;
        self.auxilliary_func_index += 1;

        let mut rng = rand::thread_rng();
        let salt = Alphanumeric.sample_string(&mut rng, 16);
        format!("__F_{:#08X}__{}", id_num, salt)
    } 


    pub fn transpile_c(&mut self) -> Result<(), Box<dyn Error>> {
        self.file.write(b"#include <stdlib.h>\n")?;
        self.file.write(b"#include <stdio.h>\n")?;
        self.file.write(b"#include <stdint.h>\n")?;
        self.file.write(b"#include \"c_libs/monad.h\"\n\n")?;

        if let SyntaxNode::Program(statements) = &self.ast.node.clone() {
            let mut statements_text: String = String::new();
            for statement in statements {
                statements_text += &self.transpile_c_tree(statement, 0)?;
            }

            // write all the auxilliary functions to the source file
            for func in &self.functions_source {
                self.file.write(func.as_bytes())?;
            }
            self.file.write(b"\n\n")?;
            
            self.file.write(statements_text.as_bytes())?;
            self.file.write(b"int main() {\n\t__special__main();\n\treturn 1;\n}\n\n")?;
            return Ok(());
        } 

        panic!("Could not transpile")
    }


    fn transpile_c_tree(&mut self, tree: &SyntaxTree, indent: usize) -> Result<String, Box<dyn Error>>{
        match &tree.node {
            SyntaxNode::Function(name, args, return_type, body) => {
                let args_string = args.iter()
                                      .map(|(p_id, p_type)| format!("{} {}", p_type.basic_type.as_ctype_str(), p_id))
                                      .collect::<Vec<String>>()
                                      .join(", ");
                let return_type_text = return_type.as_ctype_str();
                let body_text = body.iter()
                                    .map(|s| self.transpile_c_tree(s, indent + 1).unwrap())
                                    .collect::<Vec<String>>()
                                    .join("\n");
                
                // main function is a special case as it must have the return type of "int", so we
                // convert this function's name to a different name (__special__main())
                if name.as_str() == "main" {
                    return Ok(format!("\n{} __special__main() {{\n{} \n}}\n\n", return_type_text, body_text));
                }

                Ok(format!("\n{} {}({}) {{\n{} \n}}\n\n", return_type_text, name, args_string, body_text))
            }

            SyntaxNode::ReturnStmt(body) => {
                let body_text = self.transpile_c_tree(&body, indent)?;
                Ok("    ".repeat(indent) + "return " + &body_text + ";")
            }

            SyntaxNode::TernaryExpression(cond, if_true, if_false) =>
                Ok(self.transpile_c_tree(cond, indent)? + " ? " 
                    + &self.transpile_c_tree(if_true, indent)? + " : " 
                    + &self.transpile_c_tree(if_false, indent)?),
            SyntaxNode::BinaryOperation(op, l, r) => 
                Ok(self.transpile_c_tree(l, indent)? + " " + op + " " + &self.transpile_c_tree(r, indent)?),
            SyntaxNode::RightAssocUnaryOperation(op, r) => 
                Ok(op.to_owned() + " " + &self.transpile_c_tree(r, indent)?),
            SyntaxNode::LeftAssocUnaryOperation(op, l) => 
                Ok(self.transpile_c_tree(l, indent)? + " " + op),
            SyntaxNode::ParenExpr(expr) => 
                Ok("(".to_owned() + &self.transpile_c_tree(expr, indent)? + ")"),
            SyntaxNode::StringLiteral(s) => Ok(format!("\"{}\"", s)),
            SyntaxNode::IntLiteral(n) => Ok(n.to_string()),
            SyntaxNode::Identifier(id) => Ok(id.to_owned()),
            SyntaxNode::Program(_) => panic!("Got program when I should not have!"),
            SyntaxNode::FunctionCall(func_id, args) => {
                let args: Vec<String> = args.iter()
                                            .map(|arg| self.transpile_c_tree(arg, indent).unwrap())
                                            .collect();
                if func_id == &String::from("print") {
                    return Ok(format!("printf({})", args.first().unwrap()));
                }

                Ok(func_id.to_owned() + &"(".to_owned() + &args.join(", ") + &")".to_owned())
            },

            SyntaxNode::FunctionCallStmt(func_id, args) => {
                let args: Vec<String> = args.iter()
                                            .map(|arg| self.transpile_c_tree(arg, indent).unwrap())
                                            .collect();
                if func_id == &String::from("print") {
                    return Ok(format!("{}printf({});", "    ".repeat(indent), args.first().unwrap()));
                }

                Ok(format!("{}({});", "    ".repeat(indent), args.join(", ")))
            },

            SyntaxNode::SelectionStatement(cond, if_body, None) => {
                Ok(format!(
                    "{0}if ({1}) {{\n{2}\n{0}}}",
                    "    ".repeat(indent), 
                    self.transpile_c_tree(cond, indent)?,
                    if_body.iter()
                           .map(|s| self.transpile_c_tree(s, indent + 1).unwrap())
                           .collect::<Vec<String>>()
                           .join("\n")
                )) 
            }

            SyntaxNode::SelectionStatement(cond, if_body, Some(else_body)) => {
                Ok(format!(
                    "{0}if ({1}) {{\n{2}\n{0}}} else {{\n{3}\n{0}}}", 
                    "    ".repeat(indent), 
                    self.transpile_c_tree(cond, indent)?,
                    if_body.iter()
                           .map(|s| self.transpile_c_tree(s, indent + 1).unwrap())
                           .collect::<Vec<String>>()
                           .join("\n"),
                    else_body.iter()
                             .map(|s| self.transpile_c_tree(s, indent + 1).unwrap())
                             .collect::<Vec<String>>()
                             .join("\n")
                )) 
            }
            
            SyntaxNode::WhileStmt(cond, body) => {
                Ok(format!(
                    "{0}while ({1}) {{\n{2}{0}\n{0}}}\n", "    ".repeat(indent),
                    self.transpile_c_tree(cond, indent)?,
                    body.iter()
                        .map(|s| self.transpile_c_tree(s, indent + 1).unwrap())
                        .collect::<Vec<String>>()
                        .join("\n")
                ))
            }

            SyntaxNode::LetStmt(id, var_type, expr) => Ok(format!(
                "{}{} {} = {};",
                "    ".repeat(indent), 
                var_type.as_ctype_str(), 
                id, 
                self.transpile_c_tree(expr, indent)?
            )),

            SyntaxNode::ReassignmentStmt(id, expr) => Ok(format!(
                "{}{} = {};",
                "    ".repeat(indent), 
                id,
                self.transpile_c_tree(expr, indent)?
            )),

            SyntaxNode::MonadicExpr(body) => {
                let monad_func_name = self.get_next_auxilliary_func_name();
                let body_code: String = body.iter()
                                            .map(|s| self.transpile_c_tree(s, 1).unwrap())
                                            .collect::<String>();
                self.functions_source.push(
                    format!("void {}() {{\n{}\n}}", monad_func_name, body_code)
                );
                
                Ok(format!("IOMonad<void(*)()>::lift({})", monad_func_name))
            }
        }
    }
}
