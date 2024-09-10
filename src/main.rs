#![warn(missing_docs)]

//! The main crate for the compiler of the Skopje programming language.
use std::env;

mod parser;
mod transpiler;
mod semantics;

use transpiler::transpile_c::Transpiler;

use crate::parser::lexing::*;
use crate::parser::parsing::*;

fn main() {
    let cmd_args: Vec<String> = env::args().collect();
    let input_filename = match cmd_args.get(1) {
        Some(filename) => filename,
        None => panic!("No input files found!") 
    };

    let default_intermed_filename = &String::from("out.cpp");
    let intermediate_filename: &String = cmd_args.get(2).unwrap_or(default_intermed_filename);

    println!("Compiling {}...", input_filename);
    let scanner = Scanner::new(input_filename.as_str()).unwrap();
    let mut parser = Parser::new(scanner.tokens);
    match parser.parse() {
        Err(e) => eprintln!("{}", e),
        Ok(ast) => {
            let mut transpiler = Transpiler::new(ast, intermediate_filename);
            println!("{:?}", transpiler.transpile_c());
        }
    }
}
