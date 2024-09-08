#![allow(unused)]
use std::collections::VecDeque;

use crate::{SyntaxNode, SyntaxTree};

use super::token::{Token, TokenType};

struct PrattParser {
    tokens: VecDeque<Token>
}


impl PrattParser {
    fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens: VecDeque::from(tokens)
        }
    }


    fn next(&mut self) -> Option<Token> {
        return self.tokens.pop_front()
    }


    fn peek(&self) -> Option<&Token> {
        return self.tokens.front()
    }


    pub fn parse_expression(tokens: Vec<Token>) -> SyntaxTree {
        let mut parser: PrattParser = PrattParser::new(tokens);
        parser.expr_binary(0)
    }
    
    
    /// Parses a binary expression starting with the minimum precedence.
    /// 
    /// This function implements a Pratt parser that can handle expressions with various operator
    /// precedences, including prefix, infix, postfix, and ternary expressions.
    /// It uses a loop to parse a sequence of binary expressions, managing precedence and 
    /// associativity.
    ///
    /// # Arguments
    ///
    /// * `min_precedence` - The minimum precedence level that is required to continue parsing.
    /// 
    /// # Returns
    ///
    /// * `SyntaxTree` - The resulting syntax tree node representing the parsed expression.
    fn expr_binary(&mut self, min_precedence: u8) -> SyntaxTree {
        // Get the next token from the stream and start parsing the left-hand side (lhs)
        let next_token: Token = self.next().unwrap();
        let mut lhs = match next_token.token_type {
            TokenType::IntLiteral(literal) => SyntaxTree::new(
                SyntaxNode::IntLiteral(literal), 
                next_token.line_number, 
                next_token.col_number
            ),

            TokenType::Identifier(id) => SyntaxTree::new(
                SyntaxNode::Identifier(id), 
                next_token.line_number, 
                next_token.col_number
            ),

            TokenType::OpenParen => {
                let lhs: SyntaxTree = self.expr_binary(0);
                assert_eq!(self.next().unwrap().token_type, TokenType::CloseParen);
                lhs
            }

            // Handle prefix operators like `+` or `-`. Use higher precedence for the right-hand 
            // side
            TokenType::Plus | TokenType::Minus => {
                let (_, right_precedence) = prefix_precedence(&next_token.token_type);
                SyntaxTree::new(
                    SyntaxNode::RightAssocUnaryOperation(next_token.lexeme, Box::new(self.expr_binary(right_precedence))),
                0, 0)
            }

            _ => panic!("Unexpected token {:?}", next_token)
        };
        
        // Parse the infix or postfix part of the expression in a loop.
        loop {
            let next_token = self.next();
            let op = match &next_token {
                None => break,
                Some(next_token) => next_token
            };

            // Handle postfix operators (e.g., `++` or array indexing `[]`).
            if let Some((left_precedence, _)) = postfix_precedence(&op.token_type) {
                if left_precedence < min_precedence {
                    self.tokens.push_front(op.clone());
                    break;
                }
                
                lhs = match op.token_type {
                    // Handle specific postfix cases, like array indexing `[]`.
                    TokenType::OpenSquare => {
                        let rhs = self.expr_binary(0);
                        assert_eq!(self.next().unwrap().token_type, TokenType::CloseSquare);
                        SyntaxTree::new(
                            SyntaxNode::ArrayIndexingOperation(Box::new(lhs), Box::new(rhs)), 
                            0, 0
                        )
                    }

                    _ => SyntaxTree::new(
                        SyntaxNode::LeftAssocUnaryOperation(op.lexeme.clone(), Box::new(lhs)), 
                        0, 0
                    )
                };

                continue;
            }

            if let Some((left_precedence, right_precedence)) = infix_precedence(&op.token_type) {
                if left_precedence < min_precedence {
                    self.tokens.push_front(next_token.unwrap());
                    break;
                }
        
                let (line, col) = (lhs.start_line, lhs.start_index);
                lhs = match op.token_type {
                    TokenType::Question => {
                        let mhs = self.expr_binary(0);
                        assert_eq!(self.next().unwrap().token_type, TokenType::Colon);
                        let rhs = self.expr_binary(right_precedence);
                        SyntaxTree::new(SyntaxNode::TernaryExpression(
                            Box::new(lhs), 
                            Box::new(mhs), 
                            Box::new(rhs)
                        ), line, col)
                    },

                    _ => {
                        let rhs = self.expr_binary(right_precedence);
                        SyntaxTree::new(SyntaxNode::BinaryOperation(
                            op.lexeme.clone(), 
                            Box::new(lhs), 
                            Box::new(rhs)
                        ), line, col)
                    }
                };

                continue;
            }
            
            self.tokens.push_front(next_token.unwrap());
            break;
        }
    
        lhs
    }
}


fn postfix_precedence(op: &TokenType) -> Option<(u8, ())> {
    let res = match op {
        TokenType::DoublePlus | TokenType::DoubleMinus | TokenType::OpenSquare => (7, ()),
        _ => return None,
    };
    Some(res)
}


fn prefix_precedence(op: &TokenType) -> ((), u8) {
    match op {
        TokenType::Minus | TokenType::Plus | TokenType::Bang | TokenType::Complement => ((), 9),
        _ => panic!("bad op: {:?}", op)
    }
}


fn infix_precedence(op: &TokenType) -> Option<(u8, u8)> {
    match op {
        TokenType::Plus | TokenType::Minus => Some((1, 2)),
        TokenType::Question => Some((4, 3)),
        TokenType::Star | TokenType::FwdSlash => Some((5, 6)),
        _ => None
    }
}


#[cfg(test)]
mod tests {
    use crate::{Scanner, SyntaxNode, SyntaxTree};

    use super::PrattParser;

    #[test]
    fn test_parse_integer() {
        let tokens = Scanner::from_str("1".to_owned()).unwrap();
        let result = PrattParser::parse_expression(tokens.tokens);
        assert_eq!(result, SyntaxTree::new(SyntaxNode::IntLiteral(1), 0, 0))
    }


    #[test]
    fn test_basic_expression() {
        let tokens = Scanner::from_str("1 + 2 * 3".to_owned()).unwrap();
        let result = PrattParser::parse_expression(tokens.tokens);
        assert_eq!(result, SyntaxTree::new(SyntaxNode::BinaryOperation(
            "+".to_owned(), 
            Box::new(SyntaxTree::new(SyntaxNode::IntLiteral(1), 0, 0)), 
            Box::new(SyntaxTree::new(SyntaxNode::BinaryOperation(
                "*".to_owned(), 
                Box::new(SyntaxTree::new(SyntaxNode::IntLiteral(2), 0, 0)), 
                Box::new(SyntaxTree::new(SyntaxNode::IntLiteral(3), 0, 0))
            ), 0, 0))
        ), 0, 0));

        let tokens = Scanner::from_str("a + b * c * d + e".to_owned()).unwrap();
        let result = PrattParser::parse_expression(tokens.tokens);
        assert_eq!(result, SyntaxTree::new(SyntaxNode::BinaryOperation(
            "+".to_owned(),
            Box::new(SyntaxTree::new(SyntaxNode::BinaryOperation(
                "+".to_owned(), 
                Box::new(SyntaxTree::new(SyntaxNode::Identifier("a".to_owned()), 0, 0)),
                Box::new(SyntaxTree::new(SyntaxNode::BinaryOperation(
                    "*".to_owned(), 
                    Box::new(SyntaxTree::new(SyntaxNode::BinaryOperation(
                        "*".to_owned(), 
                        Box::new(SyntaxTree::new(SyntaxNode::Identifier("b".to_owned()), 0, 0)), 
                        Box::new(SyntaxTree::new(SyntaxNode::Identifier("c".to_owned()), 0, 0))
                    ), 0, 0)), 
                    Box::new(SyntaxTree::new(SyntaxNode::Identifier("d".to_owned()), 0, 0))
                ), 0, 0)),
            ), 0, 0)),
            Box::new(SyntaxTree::new(SyntaxNode::Identifier("e".to_owned()), 0, 0))
        ), 0, 0))
    }


    #[test]
    fn test_prefix_precedence() {
        let tokens = Scanner::from_str("- -1 * 2".to_owned()).unwrap();
        let result = PrattParser::parse_expression(tokens.tokens);
        assert_eq!(result, 
            SyntaxTree::new(SyntaxNode::BinaryOperation(
                "*".to_owned(), 
                Box::new(SyntaxTree::new(SyntaxNode::RightAssocUnaryOperation(
                    "-".to_owned(), 
                    Box::new(SyntaxTree::new(SyntaxNode::RightAssocUnaryOperation(
                        "-".to_owned(), 
                        Box::new(SyntaxTree::new(SyntaxNode::IntLiteral(1), 0, 0))
                    ), 0, 0))
                ), 0, 0)),
                Box::new(SyntaxTree::new(SyntaxNode::IntLiteral(2), 0, 0))
            ), 0, 0)
        )
    }


    #[test]
    fn test_postfix_operators() {
        let tokens = Scanner::from_str("-9++".to_owned()).unwrap();
        let result = PrattParser::parse_expression(tokens.tokens);
        assert_eq!(result, 
            SyntaxTree::new(SyntaxNode::LeftAssocUnaryOperation(
                "++".to_owned(), 
                Box::new(SyntaxTree::new(SyntaxNode::RightAssocUnaryOperation(
                    "-".to_owned(), 
                    Box::new(SyntaxTree::new(SyntaxNode::IntLiteral(9), 0, 0))
                ), 0, 0))
            ), 0, 0)
        );

        let tokens = Scanner::from_str("f * g++".to_owned()).unwrap();
        let result = PrattParser::parse_expression(tokens.tokens);
        assert_eq!(result, 
            SyntaxTree::new(
                SyntaxNode::BinaryOperation(
                    "*".to_owned(), 
                    Box::new(SyntaxTree::new(SyntaxNode::Identifier("f".to_owned()), 0, 0)), 
                    Box::new(SyntaxTree::new(SyntaxNode::LeftAssocUnaryOperation(
                        "++".to_owned(), 
                        Box::new(SyntaxTree::new(SyntaxNode::Identifier("g".to_owned()), 0, 0))
                    ), 0, 0))
                ), 0, 0
            )    
        );
    }


    #[test]
    fn test_parentheses() {
        let tokens = Scanner::from_str("(a + b) * c".to_owned()).unwrap();
        let result = PrattParser::parse_expression(tokens.tokens);
        assert_eq!(result,
            SyntaxTree::new(SyntaxNode::BinaryOperation(
                "*".to_owned(), 
                Box::new(SyntaxTree::new(SyntaxNode::BinaryOperation(
                    "+".to_owned(), 
                    Box::new(SyntaxTree::new(SyntaxNode::Identifier("a".to_owned()), 0, 0)), 
                    Box::new(SyntaxTree::new(SyntaxNode::Identifier("b".to_owned()), 0, 0))
                ), 0, 0)), 
                Box::new(SyntaxTree::new(SyntaxNode::Identifier("c".to_owned()), 0, 0))
            ), 0, 0)
        );

        let tokens = Scanner::from_str("(((0)))".to_owned()).unwrap();
        let result = PrattParser::parse_expression(tokens.tokens);
        assert_eq!(result, SyntaxTree::new(SyntaxNode::IntLiteral(0), 0, 0));
    }


    #[test]
    fn test_indexing() {
        let tokens = Scanner::from_str("x[0][1]".to_owned()).unwrap();
        let result = PrattParser::parse_expression(tokens.tokens);
        assert_eq!(result,
            SyntaxTree::new(SyntaxNode::ArrayIndexingOperation(
                Box::new(SyntaxTree::new(SyntaxNode::ArrayIndexingOperation(
                    Box::new(SyntaxTree::new(SyntaxNode::Identifier("x".to_owned()), 0, 0)),
                    Box::new(SyntaxTree::new(SyntaxNode::IntLiteral(0), 0, 0)),
                ), 0, 0)), 
                Box::new(SyntaxTree::new(SyntaxNode::IntLiteral(1), 0, 0)),
            ), 0, 0)
        );
    }


    #[test]
    fn test_ternary_expression() {
        let tokens = Scanner::from_str("x ? y : z".to_owned()).unwrap();
        let result = PrattParser::parse_expression(tokens.tokens);
        assert_eq!(result, 
            SyntaxTree::new(SyntaxNode::TernaryExpression(
                Box::new(SyntaxTree::new(SyntaxNode::Identifier("x".to_owned()), 0, 0)), 
                Box::new(SyntaxTree::new(SyntaxNode::Identifier("y".to_owned()), 0, 0)), 
                Box::new(SyntaxTree::new(SyntaxNode::Identifier("z".to_owned()), 0, 0))
            ), 0, 0)
        );
    }
}
