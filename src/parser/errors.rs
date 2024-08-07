use std::{fmt, error};

use super::token::Token;


#[derive(Debug, Clone)]
pub enum LexingError {
    UnrecognizedToken(String, u64, u64),
    InvalidEscapeCharacter(char),
    NonTerminatedString
}


impl fmt::Display for LexingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnrecognizedToken(token, l, c) => write!(f, "Could not recognize token {} at line {}, col {}", token, l, c),
            Self::InvalidEscapeCharacter(c) => write!(f, "{} is not a valid escape character", c),
            Self::NonTerminatedString => write!(f, "String has not been terminated")
        }
    }
}


impl error::Error for LexingError {}


#[derive(Debug, Clone)]
pub enum ParsingError {
    UnexpectedToken(Token),
    MissingSemicolon(u64),
}


impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnexpectedToken(token) => write!(f, "Unexpected token {} at line {}, col {}", 
                format!("{:?}", token.token_type), token.line_number, token.col_number + 1),
            Self::MissingSemicolon(line) => write!(f, "Missing semicolon on line {}", line),
        }
    }
}


impl error::Error for ParsingError {} 
