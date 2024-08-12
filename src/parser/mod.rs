//! This module contains everything necessary to go from a filepath to a file of source code to an
//! abstract syntax tree (AST) of that source code. That AST can then be used to create an
//! intermediate and final representation of the code.

pub mod lexing;
pub mod token;
pub mod errors;
pub mod parsing;
pub mod types;
