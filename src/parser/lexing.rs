//! Provides a struct `Scanner` for lexical analysis off a source file. 
//! `Vec<Token>`.
//! 
//! This module provides the `Scanner` struct which can perform lexical analysis of a file
//! with `Scanner::new(filename)`. The scanner struct contains several fields for the collection of 
//! debug information which is then attatched to the tokens. 
//! 
//! # Examples
//! 
//! ```
//! fn main() {
//!     let scanner: Scanner = Scanner::new("my_test_file.skj").unwrap();
//!     println!("{:#?}", scanner.tokens);
//! }
//! ```
use std::error::Error;
use std::fs::File;
use std::io::Read;

use super::errors::LexingError;
use super::token::*;


/// Contains data and methods required to lexically analyse a source code file, the output of which
/// is in the public `tokens` attribute.
/// 
/// The [`Scanner::new()`] method is used to create a [`Scanner`] instance out of a file
/// of source code which is lexed (lexically analysed) with the other methods therein. Lexing is
/// done line-by-line and the current line being lexed is tracked by the line attribute. The start
/// attribute is the index within the line at which the current token being analysed begins, and
/// the current attribute is the index in the line which is currently being analysed. The source
/// attribute is the entire source code of the file.
/// 
/// Note that the start and current attributes are 0-indexed, but the line attribute starts at 1.
/// 
/// # Examples
/// 
/// ```
/// fn main() {
///     let scanner: Scanner = Scanner::new("my_file.skj");
///     println!("{:#?}", scanner.tokens);
/// }
/// ```
pub struct Scanner {
    pub tokens: Vec<Token>, // current stream of tokens
    source: String, // the source file from which the tokens are taken
    start: u64, // the start column of the token
    current: u64, // the current position of the scanner cursor
    line: u64 // the current line in the source code being processed
}


impl Scanner {
    /// Opens the given file and performs lexical analysis to turn the contents into a stream of 
    /// tokens.
    /// 
    /// This function opens the given file, reads the contents, and passes the contents to another 
    /// function [`Scanner::scan_line()`] which converts the contents of the file to a `Vec<Token>` 
    /// value which is then returned.
    /// 
    /// # Errors
    /// 
    /// The result will return an error if:
    ///  - The file cannot be opened (e.g. does not exist)
    ///  - An invalid token is encountered
    /// 
    /// # Examples
    /// 
    /// ```
    /// fn main() {
    ///     let scanner: Scanner = Scanner::new("my_test_file.skj").unwrap();
    ///     println!("{:#?}", scanner.tokens);
    /// }
    /// ```
    pub fn new(filename: &str) -> Result<Self, Box<dyn Error>> {
        // read the contents of the file into a buffer
        let mut f = File::open(filename)?;
        let mut source = String::new();
        f.read_to_string(&mut source)?;

        let mut scanner: Self = Self { 
            source, 
            tokens: Vec::new(), 
            start: 0, 
            current: 0, 
            line: 1 
        };

        scanner.scan_file(); // generate the tokens from the source file
        Ok(scanner)
    }


    /// Lexically analyses the code in `self.source` and puts the tokens into `self.tokens`.
    /// 
    /// Goes through the source code line-by-line and passes each line to `self.scan_line()` for
    /// processing into tokens. At the end of processing each line, the line number in incremented
    /// and the start and current indexes reset to 0.
    /// 
    /// # Errors
    /// 
    /// Will have an error if an invalid token is encountered.
    /// 
    /// # Examples
    /// 
    /// For an example of use, refer to [`Scanner::new()`]
    fn scan_file(&mut self) {
        for line in self.source.clone().lines() {
            self.scan_line(line);
            self.current = 0;
            self.start = 0;
            self.line += 1;
        }
    }


    /// Lexically analyses a single line of code and places the tokens therein into `self.tokens`
    /// 
    /// Advances the current line index and then gets the text in the line between the start and
    /// current indexes. If this is all whitespace, ignore it; if it contains whitespace at the end
    /// then the current token has ended; otherwise, check if the current token has ended using
    /// [`Scanner::categorize_token()`]. If the current token has ended, then add it to self.tokens,
    /// otherwise, keep going.
    /// 
    /// # Errors
    /// 
    /// Will have an error if an invalid token is encountered.
    /// 
    /// # Examples
    /// 
    /// For an example of use, refer t0 [`Scanner::scan_file()`].
    fn scan_line(&mut self, line: &str) {
        while self.current as usize != line.len() {
            self.advance();
            let token_text = &line[self.start as usize..self.current as usize];

            // if the whole of the token is whitespace, ignore it
            if token_text.chars().into_iter().all(|c| c.is_whitespace()) {
                self.start = self.current;
                continue;
            }

            // if we have a token and we encounter whitespace and we still cannot identify the 
            // token, then that token is invalid
            if token_text.chars().into_iter().any(|c| c.is_whitespace()) {
                panic!("Could not identify token '{}' on line {}", token_text, self.line);
            }

            match self.categorize_token(token_text, line) {
                Ok(token_type) => self.add_token(token_type, line), // token is finished with
                Err(_) => () // could not categorize token, so keep going
            }
        }
    }


    /// Advances the current position in line index by 1.
    /// 
    /// # Example
    /// 
    /// ```
    /// fn check_for_arrow(&mut self, line: &str) -> Result<TokenType, String> {
    ///     if let Some('>') = self.peek(line, 0) { // check the next character
    ///         self.advance();
    ///         return Ok(TokenType::Arrow);
    ///     }
    /// 
    ///     Err("Did not find arrow!")
    /// }
    /// ```
    fn advance(&mut self) {
        self.current += 1;
    }


    /// Returns the character at the given offset from the current position in line index.
    /// 
    /// Note that if offset = 0, then the next character in the source code stream is given.
    /// 
    /// # Errors
    /// 
    /// Will return None if the line ends before the offset is reached.
    /// 
    /// # Example
    /// 
    /// ```
    /// fn check_for_arrow(&mut self, line: &str) -> Result<TokenType, String> {
    ///     if let Some('>') = self.peek(line, 0) { // check the next character
    ///         self.advance();
    ///         return Ok(TokenType::Arrow);
    ///     }
    /// 
    ///     Err("Did not find arrow!")
    /// }
    /// ```
    fn peek(&self, line: &str, offset: usize) -> Option<char> {
        line.chars().nth(self.current as usize + offset)
    }


    /// Adds a new token to `self.tokens` of the given type and resets the start of token index.
    /// 
    /// # Example
    /// 
    /// ```
    /// fn add_parenthesis(&mut self) {
    ///     self.add_token(TokenType::OpenParen, line: "(");
    /// } 
    /// ```
    fn add_token(&mut self, token_type: TokenType, line: &str) {
        let source = &line[self.start as usize..self.current as usize];
        self.tokens.push(Token::new(token_type, source.to_owned(), self.line, self.start));
        self.start = self.current;
    }


    /// Takes a string representation of a token and returns either the [`TokenType`] of the given
    /// token or an error if that is not a valid token.
    /// 
    /// If a token is potentially only partially complete, such as `=` which could be a standalone
    /// equals token or part of a `==`, `=>`, `<=`, etc... token, then the [`Scanner::peek()`]
    /// function is used to complete it and move the self.current index as necessary. This is not 
    /// done to complete identifiers, numbers, strings, or other tokens which can be of arbitrary 
    /// length.
    /// 
    /// # Errors
    /// 
    /// Returns a [`LexingError`] if the token cannot be categorized. This is used by 
    /// [`Scanner::scan_line()`] to help determine when a token is finished with.
    /// 
    /// # Examples
    /// 
    /// ```
    /// self.categorize_token("->", "fn main() -> () {");
    /// ```
    fn categorize_token(&mut self, token_text: &str, line: &str) -> Result<TokenType, LexingError> {
        match token_text {
            "(" => Ok(TokenType::OpenParen),
            ")" => Ok(TokenType::CloseParen),
            "{" => Ok(TokenType::OpenCurly),
            "}" => Ok(TokenType::CloseCurly),
            "[" => Ok(TokenType::OpenSquare),
            "]" => Ok(TokenType::CloseSquare),
            ";" => Ok(TokenType::Semicolon),
            "*" => Ok(TokenType::Star),
            "/" => Ok(TokenType::FwdSlash),
            "%" => Ok(TokenType::Percent),
            "~" => Ok(TokenType::Complement),
            "?" => Ok(TokenType::Question),
            "," => Ok(TokenType::Comma),

            "." => {
                if let Some('.') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::DoubleDot);
                }
                Ok(TokenType::Dot)
            }

            ":" => {
                if let Some(':') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::DoubleColon);
                }
                Ok(TokenType::Colon)
            }

            "+" => {
                if let Some('+') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::DoublePlus);
                }
                Ok(TokenType::Plus)
            },

            "-" => { // this could be a minus or an arrow -> depending on the next character
                if let Some('>') = self.peek(line, 0) { // check the next character
                    // advance and return an arrow token if the - is followed by a >
                    self.advance();
                    return Ok(TokenType::Arrow);
                } else if let Some('-') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::DoubleMinus);
                }

                Ok(TokenType::Minus)
            }

            ">" => {
                if let Some('>') = self.peek(line, 0) {
                    self.advance();
                    if let Some('>') = self.peek(line, 0) {
                        self.advance();
                        return Ok(TokenType::TripleRightArrow);
                    }

                    return Ok(TokenType::DoubleRightArrow);
                } else if let Some('=') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::RightArrowEqual);
                } else {
                    return Ok(TokenType::RightArrow)
                }
            }

            "<" => {
                if let Some('<') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::DoubleLeftArrow);
                } else if let Some('=') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::LeftArrowEqual);
                } else {
                    return Ok(TokenType::LeftArrow);
                }
            }

            "=" => {
                if let Some('=') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::DoubleEqual);
                } else {
                    return Ok(TokenType::Equal);
                }
            }

            "!" => {
                if let Some('=') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::BangEqual);
                } else {
                    return Ok(TokenType::Bang);
                } 
            }

            "&" => {
                if let Some('&') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::DoubleAmpersand);
                } else {
                    return Ok(TokenType::Ampersand);
                } 
            }

            "|" => {
                if let Some('|') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::DoublePipe);
                } else {
                    return Ok(TokenType::Pipe);
                } 
            }

            "^" => {
                if let Some('^') = self.peek(line, 0) {
                    self.advance();
                    return Ok(TokenType::DoubleUpArrow);
                } else {
                    return Ok(TokenType::UpArrow);
                } 
            }

            "\"" => self.tokenize_string(line),

            _ => {
                // check if this token is a valid identifier
                if is_valid_identifier(token_text) {
                    // check if this is the end of the identifier by checking if the next character
                    // would also be valid as part of an identifier.
                    let next_char = &self.peek(line, 0).unwrap_or('\0').to_string();
                    if !is_valid_identifier(&(token_text.to_owned() + next_char)) { // if yes, check if it is a keyword
                        match token_text {
                            "fn" => return Ok(TokenType::FnKeyword),
                            "return" => return Ok(TokenType::ReturnKeyword),
                            "if" => return  Ok(TokenType::IfKeyword),
                            "else" => return Ok(TokenType::ElseKeyword),
                            "while" => return Ok(TokenType::WhileKeyword),
                            "for" => return Ok(TokenType::ForKeyword),
                            "in" => return Ok(TokenType::InKeyword),
                            "let" => return Ok(TokenType::LetKeyword),
                            "do" => return Ok(TokenType::DoKeyword),
                            "true" => return Ok(TokenType::BoolLiteral(true)),
                            "false" => return Ok(TokenType::BoolLiteral(false)),
                            // is not a keyword, and therefore is an identifier
                            _ => return Ok(TokenType::Identifier(token_text.to_owned()))
                        }
                    }
                }

                
                if token_text.chars().all(|c| c.is_numeric()) && !self.peek(line, 0).unwrap_or('\0').is_numeric() {
                    return Ok(TokenType::IntLiteral(token_text.parse::<u64>().unwrap()));
                }

                // this is the end of a token, but the token is not valid
                Err(LexingError::UnrecognizedToken(token_text.to_owned(), self.line, self.start))
            }
        }
    }


    /// Creates a string token from the source text, assuming that the first '"' character has
    /// already been encountered.
    /// 
    /// Will permit the use of escape characters '\0', '\n', '\r', '\t', '\\' and '\"', and ends the 
    /// token at the first unescaped '"' character encountered.
    /// 
    /// # Errors
    /// 
    /// Will return an error if no final '"' character is found.
    /// 
    /// # Examples
    /// ```
    /// // assume that the lexer has just encountered a '"'
    /// self.parse_string()
    /// ```
    fn tokenize_string(&mut self, line: &str) -> Result<TokenType, LexingError> {
        let mut string: String = String::new();

        loop {
            // advance and check that we have not reached the end of the line without ending the
            // string
            self.advance();
            let token_text: &str = if self.current as usize <= line.len() {
                &line[self.start as usize..self.current as usize]
            } else {
                return Err(LexingError::NonTerminatedString);
            };

            // check if we have an escaped character to handle, if so, handle it and advance again
            if token_text.chars().last().unwrap() == '\\' {
                match self.peek(line, 0).unwrap() {
                    '\\' => string += "\\\\",
                    '"' => string += "\\\"",
                    't' => string += "\\t",
                    'n' => string += "\\n",
                    'r' => string += "\\r",
                    '0' => string += "\\0",
                    c => return Err(LexingError::InvalidEscapeCharacter(c))
                }

                self.advance();
            } else if token_text.chars().last().unwrap() == '"' { // end of the string
                break;
            } else { // add a normal character
                string.push(token_text.chars().last().unwrap());
            }
        }

        self.start = self.current;
        Ok(TokenType::StrLiteral(string))
    }
}


/// Returns true if the given string is a valid identifier, and false otherwise.
/// 
/// Returns true if the passed identifier:
///  - contains only alphanumeric characters and '_'
///  - begins with either an alphabetic character or an underscore
/// 
/// # Examples
/// 
/// ```
/// assert!(is_valid_identifier("my_var"));
/// assert!(is_valid_identifier("_thisIsValid"));
/// assert!(!is_valid_identifier("0NotValid"));
/// assert!(!is_valid_identifier("Bad?Identifier"));
/// ```
fn is_valid_identifier(c: &str) -> bool {
    if !c.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return false;
    }

    if c.chars().nth(0).unwrap() != '_' && !c.chars().nth(0).unwrap().is_alphabetic() {
        return false;
    }

    true
}
