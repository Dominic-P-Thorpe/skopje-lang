#![warn(missing_docs)]

//! The main crate for the compiler of the Skopje programming language.
mod parser;
mod transpiler;
mod semantics;

use transpiler::transpile_c::Transpiler;

use crate::parser::lexing::*;
use crate::parser::parsing::*;

fn main() {
    let scanner = Scanner::new("my_file.skj").unwrap();
    // println!("Tokens: {:#?}", scanner.tokens);
    let mut parser = Parser::new(scanner.tokens);
    let ast = parser.parse().unwrap();
    println!("{:#?}", ast);
    let mut transpiler = Transpiler::new(ast, "out.cpp");
    println!("{:#?}", transpiler.transpile_c().unwrap());
}
