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
use std::error::Error;
use std::fs::{File, OpenOptions};
use std::io::Write;

use crate::{SyntaxNode, SyntaxTree};


/// The core of the transpiler module, containing data and methods needed to transpile from Skopje
/// to C code.
pub struct Transpiler {
    /// The target file to write the C code to
    file: File,
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
            ast: source 
        }
    }


    pub fn transpile_c(&mut self) -> Result<(), Box<dyn Error>> {
        self.file.write(b"#include<stdlib.h>\n")?;
        self.file.write(b"#include<stdio.h>\n")?;
        self.file.write(b"#include<stdint.h>\n\n")?;

        if let SyntaxNode::Program(statements) = &self.ast.node {
            let mut statements_text: String = String::new();
            for statement in statements {
                statements_text += &Transpiler::transpile_c_tree(statement, 0)?;
            }

            self.file.write(statements_text.as_bytes())?;
            return Ok(());
        } 

        panic!("Could not transpile")
    }


    fn transpile_c_tree(tree: &SyntaxTree, indent: usize) -> Result<String, Box<dyn Error>>{
        match &tree.node {
            SyntaxNode::Function(name, args, return_type, body) => {
                let args_string = args.iter()
                                      .map(|(p_id, p_type)| format!("{} {}", Transpiler::convert_type_to_ctype(&p_type.basic_type), p_id))
                                      .collect::<Vec<String>>()
                                      .join(", ");
                let return_type_text = Transpiler::convert_type_to_ctype(&return_type.basic_type);
                let body_text = body.iter()
                                    .map(|s| Transpiler::transpile_c_tree(s, indent + 1).unwrap())
                                    .collect::<Vec<String>>()
                                    .join("\n");
                Ok("\n".to_owned() + &return_type_text.to_string() + " " + name + "(" + &args_string + ")" + " {\n" + &body_text + "\n}\n\n")
            }

            SyntaxNode::ReturnStmt(body) => {
                let body_text = Transpiler::transpile_c_tree(&body, indent)?;
                Ok("    ".repeat(indent) + "return " + &body_text + ";")
            }

            SyntaxNode::TernaryExpression(cond, if_true, if_false) =>
                Ok(Transpiler::transpile_c_tree(cond, indent)? + " ? " 
                    + &Transpiler::transpile_c_tree(if_true, indent)? + " : " 
                    + &Transpiler::transpile_c_tree(if_false, indent)?),
            SyntaxNode::BinaryOperation(op, l, r) => 
                Ok(Transpiler::transpile_c_tree(l, indent)? + " " + op + " " + &Transpiler::transpile_c_tree(r, indent)?),
            SyntaxNode::RightAssocUnaryOperation(op, r) => 
                Ok(op.to_owned() + " " + &Transpiler::transpile_c_tree(r, indent)?),
            SyntaxNode::LeftAssocUnaryOperation(op, l) => 
                Ok(Transpiler::transpile_c_tree(l, indent)? + " " + op),
            SyntaxNode::ParenExpr(expr) => 
                Ok("(".to_owned() + &Transpiler::transpile_c_tree(expr, indent)? + ")"),
            SyntaxNode::StringLiteral(s) => Ok(format!("\"{}\"", s)),
            SyntaxNode::IntLiteral(n) => Ok(n.to_string()),
            SyntaxNode::Identifier(id) => Ok(id.to_owned()),
            SyntaxNode::Program(_) => panic!("Got program when I should not have!"),
            SyntaxNode::FunctionCall(func_id, args) => {
                let args: Vec<String> = args.iter()
                                            .map(|arg| Transpiler::transpile_c_tree(arg, indent).unwrap())
                                            .collect();
                if func_id == &String::from("print") {
                    return Ok(format!("printf({})", args.first().unwrap()));
                }

                Ok(func_id.to_owned() + &"(".to_owned() + &args.join(", ") + &")".to_owned())
            },

            SyntaxNode::FunctionCallStmt(func_id, args) => {
                let args: Vec<String> = args.iter()
                                            .map(|arg| Transpiler::transpile_c_tree(arg, indent).unwrap())
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
                    Transpiler::transpile_c_tree(cond, indent)?,
                    if_body.iter()
                           .map(|s| Transpiler::transpile_c_tree(s, indent + 1).unwrap())
                           .collect::<Vec<String>>()
                           .join("\n")
                )) 
            }

            SyntaxNode::SelectionStatement(cond, if_body, Some(else_body)) => {
                Ok(format!(
                    "{0}if ({1}) {{\n{2}\n{0}}} else {{\n{3}\n{0}}}", 
                    "    ".repeat(indent), 
                    Transpiler::transpile_c_tree(cond, indent)?,
                    if_body.iter()
                           .map(|s| Transpiler::transpile_c_tree(s, indent + 1).unwrap())
                           .collect::<Vec<String>>()
                           .join("\n"),
                    else_body.iter()
                             .map(|s| Transpiler::transpile_c_tree(s, indent + 1).unwrap())
                             .collect::<Vec<String>>()
                             .join("\n")
                )) 
            }

            
            SyntaxNode::WhileStmt(cond, body) => {
                Ok(format!(
                    "{0}while ({1}) {{\n{2}{0}\n{0}}}\n", "    ".repeat(indent),
                    Transpiler::transpile_c_tree(cond, indent)?,
                    body.iter()
                        .map(|s| Transpiler::transpile_c_tree(s, indent + 1).unwrap())
                        .collect::<Vec<String>>()
                        .join("\n")
                ))
            }
        }
    }


    /// Converts Skopje types to their closest equivalents in C using the stdint.h library.
    fn convert_type_to_ctype(original: &str) -> &str {
        match original {
            "i32" => "int32_t",
            "u32" => "uint32_t",
            "str" => "char*",
            _ => panic!("Unrecognized type")
        }
    }
}
