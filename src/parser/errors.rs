use std::{fmt, error};

use crate::SyntaxTree;

use super::{token::{Token, TokenType}, types::Type};


#[derive(Debug, Clone)]
pub enum LexingError {
    UnrecognizedToken(String, usize, usize),
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


#[allow(unused)]
#[derive(Debug, Clone)]
pub enum ExpectedToken {
    ParseToken(TokenType),
    Expression,
    Statement,
    Identifier,
    ConstantExpression,
    Operator,
    Literal,
    FnKeyword,
    InKeyword,
    Colon,
    Comma,
    OpenParen,
    CloseParen,
    OpenSquare,
    CloseSquare,
    OpenCurly,
    CloseCurly,
    LeftArrow,
    RightArrow,
    Arrow,
    Equal,
    Semicolon,
    DoubleColon,
    ThickArrow,
    Dot
}


#[allow(unused)]
#[derive(Debug, Clone)]
pub enum ParsingError {
    // token encountered, token expected
    UnexpectedToken(Token, ExpectedToken),
    MissingSemicolon(usize),
    InvalidTypeName(String),
    ReturnTypeMismatch(Type, Type, usize, usize),
    EarlyReturn(SyntaxTree)
}


impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnexpectedToken(token, expected) => write!(f, "Unexpected token {} at line {}, col {}, expected {:?}", 
                format!("{:?}", token.token_type), token.line_number, token.col_number + 1, expected),
            Self::MissingSemicolon(line) => write!(f, "Missing semicolon on line {}", line),
            Self::InvalidTypeName(name) => write!(f, "{} is not a valid type name", name),
            Self::ReturnTypeMismatch(got, expected, line, col) => 
                write!(f, "Type mismatch at line {}, col {}, expected {:?}, got {:?}", line, col, expected.basic_type, got.basic_type),
            Self::EarlyReturn(_) => write!(f, "Unexpected EOF encountered!")
        }
    }
}


impl error::Error for ParsingError {} 
