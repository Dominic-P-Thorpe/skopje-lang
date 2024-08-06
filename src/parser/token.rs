//! Provides a representation of the tokens of the language which include debugging information
//! which can be used to display useful error messages, and the data needed to produce the abstract
//! syntax tree.
use std::fmt;


/// All the possible types of tokens that a token may take in Skopje (minus any yet to be 
/// implemented).
/// 
/// The values of literals and identifiers are contained within their variant.
#[derive(Debug, Clone, PartialEq)]
pub enum TokenType {
    OpenParen,
    CloseParen,
    OpenCurly,
    CloseCurly,
    Arrow,
    Semicolon,
    Plus,
    DoublePlus,
    Minus,
    DoubleMinus,
    Star,
    FwdSlash,
    Percent,
    RightArrow,
    DoubleRightArrow,
    TripleRightArrow,
    RightArrowEqual,
    LeftArrow,
    DoubleLeftArrow,
    LeftArrowEqual,
    Equal,
    DoubleEqual,
    Complement,
    Bang,
    BangEqual,
    Ampersand,
    DoubleAmpersand,
    Pipe,
    DoublePipe,
    UpArrow,
    DoubleUpArrow,
    Question,
    Colon,
    Comma,
    FnKeyword,
    ReturnKeyword,
    IntLiteral(u64),
    Identifier(String)
}


/// Metadata for tokens required for parsing and debugging/error messages
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub token_type: TokenType,
    pub lexeme: String,
    pub line_number: u64,
    pub col_number: u64
}


impl Token {
    /// Creates a new token from the information passed as arguments.
    /// 
    /// # Examples
    /// 
    /// ```
    /// Token::new(TokenType::Identifier("my_id"), "my_id".to_owned(), 5, 20);
    /// ```
    pub fn new(token_type: TokenType, lexeme: String, line_number: u64, col_number: u64) -> Self {
        Self {
            token_type, lexeme, line_number, col_number
        }
    }


    /// Converts the token to a textual representation of it, including making the column number
    /// 1-indexed.
    /// 
    /// # Examples
    /// 
    /// ```
    /// let token = Token::new(TokenType::Semicolon, ";".to_owned(), 10, 20);
    /// assert_eq!(token.to_string(), "Semicolon ';' at (10, 21)");
    /// ```
    pub fn to_string(self: &Self) -> String {
        format!("{:?} {} at ({}, {})", self.token_type, self.lexeme, self.line_number, self.col_number + 1)
    }
}


impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}
