use std::cell::RefCell;
use std::collections::VecDeque;
use std::error::Error;
use std::rc::Rc;

use indexmap::IndexMap;
use rand::distributions::{Alphanumeric, DistString};

use crate::semantics::symbol_table::{Symbol, SymbolTable, SymbolType};
use crate::semantics::typechecking::*;

use super::types::SimpleType;
use super::errors::{ParsingError, ExpectedToken};
use super::{token::*, types::Type};


macro_rules! parse_binary_operator {
    ($self:ident, $next:ident, $($op_type:ident => $op_str:expr),*) => {{
        let mut root: SyntaxTree = $self.$next()?;
        let (root_line, root_col) = (root.start_line, root.start_index);

        loop {
            let next_token = $self.tokens.pop_front().unwrap();
            match next_token.token_type {
                $(
                    TokenType::$op_type => {
                        let right: SyntaxTree = $self.$next()?;
                        root = SyntaxTree::new(SyntaxNode::BinaryOperation(
                            $op_str.to_owned(),
                            Box::new(root),
                            Box::new(right),
                        ), root_line, root_col);
                    }
                )*

                // End of this level of precedence
                _ => {
                    $self.tokens.push_front(next_token);
                    break;
                }
            }
        }

        Ok(root)
    }};
}


macro_rules! assert_token_type {
    ($token:ident, $token_type:ident) => {
        match $token.token_type {
            TokenType::$token_type => (),
            _ => return Err(Box::new(
                ParsingError::UnexpectedToken($token, ExpectedToken::$token_type)
            ))
        }
    };
}


#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    // enum name, pattern name, pattern data params
    EnumPattern(String, String, Vec<Pattern>),
    IdentifierPattern(String),
    // the sub-patterns within the tuple to match
    TuplePattern(String, Vec<Pattern>),
    ArrayPattern(String, Vec<Pattern>, Box<Option<Pattern>>),
    LessThanEqRangePattern(String, i64),
    GreaterThanEqRangePattern(String, i64),
    BetweenEqRangePattern(String, i64, i64),
    // placeholder name for the pattern variable, value of the literal
    IntLiteralPattern(String, i64),
    StrLiteralPattern(String, String),
    BoolLiteralPattern(String, bool)
}


#[derive(Debug, Clone)]
pub enum SyntaxNode {
    Program(Box<SyntaxTree>),
    // name, variants
    Enumeraion(String, Vec<SyntaxTree>),
    // name, parameters (param name, param type)
    EnumVariant(String, IndexMap<String, Type>),
    // Enum type, variant name, variant arguments
    EnumInstantiation(Type, String, IndexMap<String, SyntaxTree>),
    // function name, arguments (id, type), return type, body statements
    Function(String, Vec<(String, Type)>, Type, Box<SyntaxTree>),
    // expression to return
    ReturnStmt(Box<SyntaxTree>),
    // condition, body
    WhileStmt(Box<SyntaxTree>, Box<SyntaxTree>),
    // Loop variable name, loop var type, expr to loop over, loop body
    ForStmt(String, Type, Box<SyntaxTree>, Box<SyntaxTree>),
    // expression to match, patterns to match against and syntax tree to run if match succeeds,
    // type of the expression to match
    // Members of vector of patterns are a tuple where the first element is a vector of patterns
    // and the second is the body to run if any of those patterns are a match
    MatchStmt(Box<SyntaxTree>, Vec<(Vec<Pattern>, SyntaxTree)>, Type),
    // variable name, type, expression
    LetStmt(String, Type, Box<SyntaxTree>),
    // variable name, new value expression, type of the variable being reassigned
    // type is needed so that is can be used when generating the C++ code
    ReassignmentStmt(Box<SyntaxTree>, Box<SyntaxTree>, Type),
    // condition, body, optional else
    SelectionStatement(Box<SyntaxTree>, Box<SyntaxTree>, Box<Option<SyntaxTree>>),
    // binary operation, left side, right side
    BinaryOperation(String, Box<SyntaxTree>, Box<SyntaxTree>),
    RightAssocUnaryOperation(String, Box<SyntaxTree>),
    LeftAssocUnaryOperation(String, Box<SyntaxTree>),
    TupleIndexingOperation(Box<SyntaxTree>, Box<SyntaxTree>),
    // index to get, stmt to index
    ArrayIndexingOperation(Box<SyntaxTree>, Box<SyntaxTree>),
    // array to get subarray of, type of original array, start index, end index
    SubarrayOperation(Box<SyntaxTree>, Type, usize, usize),
    // condition, value if true, value if false
    TernaryExpression(Box<SyntaxTree>, Box<SyntaxTree>, Box<SyntaxTree>),
    ParenExpr(Box<SyntaxTree>),
    MonadicExpr(Box<SyntaxTree>),
    // function name, arguments
    FunctionCall(String, Vec<SyntaxTree>),
    FunctionCallStmt(String, Vec<SyntaxTree>),
    StringLiteral(String),
    IntLiteral(u64),
    BoolLiteral(bool),
    TupleLiteral(Vec<SyntaxTree>),
    ArrayLiteral(Vec<SyntaxTree>, Type),
    // store the type so that if the type is an std::unique_ptr we know to use std::move when we 
    // want to use it
    Identifier(String),
    // a block of statements represented as a vec, and a pointer to the symbol table of that block
    StmtBlock(Vec<SyntaxTree>, Rc<RefCell<SymbolTable>>)
}


#[derive(Debug, Clone)]
pub struct SyntaxTree {
    pub node: SyntaxNode,
    pub start_index: usize,
    pub start_line: usize
}


impl SyntaxTree {
    pub fn new(node: SyntaxNode, start_line: usize, start_index: usize) -> Self {
        SyntaxTree {
            node, start_index, start_line
        }
    }
}


/// Contains a [`VecDeque`] of tokens which can be used as a FIFO queue data structure. 
/// 
/// This data structure is modified by the parser as tokens are sequentially popped off of the front
/// of the queue and organized into the AST.
pub struct Parser {
    tokens: VecDeque<Token>,
    symbol_table_root: Rc<RefCell<SymbolTable>>,
    current_symbol_table: Rc<RefCell<SymbolTable>>,
    auxilliary_var_index: usize
}


impl Parser {
    /// Creates a [`VecDeque`] of tokens which can be used as a FIFO queue data structure in the
    /// [`Parser`] struct.  
    pub fn new(tokens: Vec<Token>) -> Self {
        let symbol_table_root = SymbolTable::new(None);
        let parser = Parser { 
            tokens: VecDeque::from(tokens),
            symbol_table_root: symbol_table_root.clone(),
            current_symbol_table: symbol_table_root,
            auxilliary_var_index: 0
        };

        let print_type = Type::from_basic(
            SimpleType::Function(
                Box::new(Type::from_basic(SimpleType::Void)), 
                vec![Type::from_basic(SimpleType::Str)]
            )
        );

        parser.symbol_table_root.borrow_mut().insert(
            Symbol::new(SymbolType::Function("print".to_owned(), print_type), 0, 0)
        );
        parser
    }


    pub fn parse(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        let mut top_level_constructs: Vec<SyntaxTree> = vec![];
        while let Some(next_token) = self.tokens.pop_front() {
            match &next_token.token_type {
                TokenType::FnKeyword => top_level_constructs.push(self.parse_function(next_token.line_number, next_token.col_number)?),
                TokenType::EnumKeyword => top_level_constructs.push(self.parse_enumeration(next_token.line_number, next_token.col_number)?),
                _ => panic!()
            }
        }

        let program_block = SyntaxTree::new(SyntaxNode::StmtBlock(top_level_constructs, self.symbol_table_root.clone()), 0, 0);
        Ok(SyntaxTree::new(SyntaxNode::Program(Box::new(program_block)), 0, 0))
    }


    /// Generates a unique, random variable name.
    ///
    /// This function creates a unique variable name by combining a sequential index with a randomly 
    /// generated alphanumeric string. The generated name is intended to be used as an auxiliary or 
    /// temporary variable in code generation or similar contexts where unique identifiers are 
    /// required.
    ///
    /// # Returns
    ///
    /// A `String` representing the unique variable name. The format of the name is:
    /// `"__F_{:#08X}__<random_string>"`, where:
    ///     - `{:#08X}` is the zero-padded, hexadecimal representation of an internal counter 
    /// (`auxiliary_var_index`).
    ///     - `<random_string>` is a 16-character long randomly generated alphanumeric string.
    ///
    /// # Notes
    ///
    /// - The internal counter (`auxiliary_var_index`) is incremented each time the function is 
    /// called, ensuring that the generated names are sequentially unique.
    fn generate_random_variable(&mut self) -> String {
        let id_num: usize = self.auxilliary_var_index;
        self.auxilliary_var_index += 1;

        let mut rng = rand::thread_rng();
        let salt = Alphanumeric.sample_string(&mut rng, 16);
        format!("__V_{:#08X}__{}", id_num, salt)
    } 


    /// Parses a function which may have arguments and a return type.
    /// 
    /// The function has the following EBNF grammar: 
    /// 
    /// `function ::= 'fn' <identifier> '(' [{<identifier> ':' <type>} <identifier> ':' <type>] ')' -> <type> '{' {statements} '}'`
    /// 
    /// # Grammar Example
    /// 
    /// Some examples of a valid function in Skopje are:
    /// ```
    /// fn main() -> IO<()> {
    ///     print("Hello world!");
    /// }
    /// ```
    /// 
    /// ```
    /// fn read_file_lines(file: 'File) -> IO<[str]> {
    ///     do {
    ///         let contents: str = snd read(file);
    ///         return split(contents, '\n');
    ///     }
    /// }
    /// ```
    fn parse_function(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        let id_token = self.tokens.pop_front().unwrap();
        if let TokenType::Identifier(id) = id_token.token_type {
            let open_paren = self.tokens.pop_front().unwrap();
            assert_token_type!(open_paren, OpenParen);

            let params: Vec<(String, Type)> = self.parse_func_params()?;

            let arrow = self.tokens.pop_front().unwrap();
            assert_token_type!(arrow, Arrow);

            let return_type = self.parse_type().unwrap();

            let open_body = self.tokens.pop_front().unwrap();
            assert_token_type!(open_body, OpenCurly);
            
            let body = self.parse_stmt_block(vec![])?;
            
            let close_body = self.tokens.pop_front().unwrap();
            assert_token_type!(close_body, CloseCurly);
            
            // add this function to the valid functions available in this context
            let func_type = Type::new(SimpleType::Function(
                Box::new(return_type.clone()), params.iter().map(|(_, t)| t).cloned().collect::<Vec<Type>>()
            ), false, vec![]);
            self.current_symbol_table.borrow_mut().insert(Symbol::new(SymbolType::Function(id.clone(), func_type), line_num, col_num));
            return Ok(SyntaxTree::new(
                SyntaxNode::Function(id, params, return_type, Box::new(body)), line_num, col_num
            ));
        }

        Err(Box::new(ParsingError::UnexpectedToken(id_token, super::errors::ExpectedToken::Identifier)))
    }


    fn parse_func_params(&mut self) -> Result<Vec<(String, Type)>, Box<dyn Error>> {
        let mut params: Vec<(String, Type)> = vec![];
        let next_token = self.tokens.pop_front().unwrap();
        // return an empty vec if there are no parameters
        if let TokenType::CloseParen = next_token.token_type {
            return Ok(vec![]);
        }

        // put token back so it can be included as the first parameter's name
        self.tokens.push_front(next_token);

        // get all the params into the vec (which are comma separated) until the last ")" token 
        // is reached
        loop {
            let next_token = self.tokens.pop_front().unwrap();
            let (p_id, p_line, p_col) = if let TokenType::Identifier(id) = next_token.token_type {
                (id, next_token.line_number, next_token.col_number)
            } else {
                return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier)));
            };

            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Colon => (),
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Colon)))
            }

            // TODO: make this work with all param types
            let p_type: Type = self.parse_type().unwrap();

            params.push((p_id.clone(), p_type.clone()));
            self.current_symbol_table.borrow_mut().insert(Symbol::new(SymbolType::Variable(p_id, p_type), p_line, p_col));

            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::CloseParen => break,
                TokenType::Comma => continue,
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen)))
            }
        }

        Ok(params)
    }


    /// Parses the body of a function, which is any number of statements of the following 
    /// categories:
    ///  - return statements,
    ///  - function calls,
    ///  - for and while loops,
    ///  - match statements,
    ///  - variable declarations and reassignments
    ///  - expressions
    ///  - if-else statements
    fn parse_stmt_block(&mut self, new_symbols: Vec<Symbol>) -> Result<SyntaxTree, Box<dyn Error>> {
        self.current_symbol_table = SymbolTable::add_child(&self.current_symbol_table);
        for symbol in new_symbols {
            self.current_symbol_table.borrow_mut().insert(symbol);
        }

        let mut statements: Vec<SyntaxTree> = vec![];
        loop {
            let statement = self.parse_statement()?;
            statements.push(statement);

            if let TokenType::CloseCurly = self.tokens.get(0).unwrap().token_type {
                break;
            }
        }

        let (start_line, start_index) = (statements.first().unwrap().start_line, statements.first().unwrap().start_index);

        let parent_symbol_table = self.current_symbol_table.borrow()
                                                                                     .parent.as_ref().unwrap()
                                                                                     .upgrade().unwrap();
        self.current_symbol_table = parent_symbol_table;
        Ok(SyntaxTree::new(
            SyntaxNode::StmtBlock(statements, self.current_symbol_table.clone()), 
            start_line, start_index
        ))
    }


    fn parse_statement(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::ReturnKeyword => self.parse_return(next_token.line_number, next_token.col_number),
            TokenType::IfKeyword => self.parse_selection(next_token.line_number, next_token.col_number),
            TokenType::WhileKeyword => self.parse_while_loop(next_token.line_number, next_token.col_number),
            TokenType::Identifier(id) => self.parse_func_call_or_reassignment_stmt(id, next_token.line_number, next_token.col_number),
            TokenType::LetKeyword => self.parse_let_statement(next_token.line_number, next_token.col_number),
            TokenType::ForKeyword => self.parse_for_loop(next_token.line_number, next_token.col_number),
            TokenType::MatchKeyword => self.parse_match_stmt(next_token.line_number, next_token.col_number),
            _ => Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Statement)))
        }
    }


    fn parse_match_stmt(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        let match_expr = self.parse_expression()?;
        let match_expr_type = get_expr_type(&match_expr, &self.current_symbol_table.borrow())?;

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenCurly);

        let patterns = self.parse_match_patterns(&match_expr_type)?;

        Ok(SyntaxTree::new(SyntaxNode::MatchStmt(
            Box::new(match_expr), 
            patterns,
            match_expr_type
        ), 
        line_num, col_num))
    }


    fn parse_match_patterns(&mut self, match_expr_type: &Type) -> Result<Vec<(Vec<Pattern>, SyntaxTree)>, Box<dyn Error>> {
        let mut patterns: Vec<(Vec<Pattern>, SyntaxTree)> = vec![];
        loop {
            let next_token = self.tokens.front().unwrap();
            let (line_num, col_num) = (next_token.line_number, next_token.col_number);
            let pattern = self.parse_match_pattern()?;

            let next_token = self.tokens.pop_front().unwrap();
            assert_token_type!(next_token, ThickArrow);
            let next_token = self.tokens.pop_front().unwrap();
            assert_token_type!(next_token, OpenCurly);

            let new_symbols: Vec<Symbol> = self.get_pattern_symbols(&pattern, match_expr_type, line_num, col_num);

            let statement_block: SyntaxTree = self.parse_stmt_block(new_symbols)?;

            let next_token = self.tokens.pop_front().unwrap();
            assert_token_type!(next_token, CloseCurly);

            patterns.push((vec![pattern], statement_block));

            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseCurly => break,
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseCurly)))
            }
        }

        Ok(patterns)
    }


    fn get_pattern_symbols(&mut self, pattern: &Pattern, match_expr_type: &Type, line_num: usize, col_num: usize) -> Vec<Symbol> {
        match &pattern {
            Pattern::EnumPattern(enum_name, variant_name, _) => {
                let enum_type: Type = self.current_symbol_table.borrow().get(enum_name).unwrap().get_type();
                let expected_params = match &enum_type.basic_type {
                    SimpleType::Enum(_, variants, _) => 
                        variants.get(variant_name).unwrap(),
                    _ => panic!()
                };

                let data_params = self.get_data_params_from_enum_pattern(&pattern, &enum_type, variant_name, line_num, col_num);
                assert_eq!(data_params.len(), expected_params.len());
                data_params
            }

            Pattern::IdentifierPattern(id) => 
                vec![Symbol::new(SymbolType::Variable(id.to_owned(), match_expr_type.clone()), line_num, col_num)],
            
            Pattern::TuplePattern(_, patterns) => {
                let mut new_symbols: Vec<Symbol> = vec![];
                for i in 0..patterns.len() {
                    let pattern= patterns.get(i).unwrap();
                    let member_type: &Type = match &match_expr_type.basic_type {
                        SimpleType::Tuple(types) => types.get(i).unwrap(),
                        _ => panic!()
                    };

                    match pattern {
                        Pattern::IdentifierPattern(id) => 
                            new_symbols.push(Symbol::new(SymbolType::Variable(id.to_string(), member_type.clone()), line_num, col_num)),
                        _ => ()
                    }
                }

                new_symbols
            }

            Pattern::ArrayPattern(_, patterns, end) => {
                let mut new_symbols: Vec<Symbol> = vec![];
                let member_type: Type = get_array_inner_type(&match_expr_type);
                for pattern in patterns {
                    match pattern {
                        Pattern::IdentifierPattern(id) => 
                            new_symbols.push(Symbol::new(SymbolType::Variable(id.to_string(), member_type.clone()), line_num, col_num)),
                        _ => ()
                    }
                }

                match &**end {
                    None => (),
                    Some(p) => match p {
                        Pattern::IdentifierPattern(id) => 
                            new_symbols.push(Symbol::new(SymbolType::Variable(id.to_string(), member_type.clone()), line_num, col_num)),
                        _ => ()
                    }
                }

                new_symbols
            }

            _ => vec![]
        }
    }


    fn get_data_params_from_enum_pattern(
        &mut self, 
        pattern: &Pattern, 
        enum_type: &Type, 
        variant_name: &str, 
        line_num: usize, 
        col_num: usize
    ) -> Vec<Symbol> {
        let mut result: Vec<Symbol> = vec![];
        let variant_data_params = match &enum_type.basic_type {
            SimpleType::Enum(_, variants, _) => variants.get(variant_name).unwrap(),
            _ => panic!()
        };

        match pattern {
            // param patterns is the name assigned to the variable in the enum pattern, not the
            // enum declaration
            Pattern::EnumPattern(_, _, param_patterns) => {
                for i in 0..param_patterns.len() {
                    let param_name = match param_patterns.get(i).unwrap() {
                        Pattern::IdentifierPattern(id)
                        | Pattern::BoolLiteralPattern(id, _)
                        | Pattern::IntLiteralPattern(id, _)
                        | Pattern::StrLiteralPattern(id, _) 
                        | Pattern::TuplePattern(id, _) => id,
                        _ => panic!()
                    };

                    let param_type = variant_data_params.get_index(i).unwrap().1;
                    result.push(Symbol::new(
                        SymbolType::Variable(param_name.to_string(), param_type.clone()), 
                        line_num, col_num)
                    );
                }
            }

            _ => panic!()
        }

        result
    }


    fn parse_match_pattern(&mut self) -> Result<Pattern, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::Identifier(enum_name) => self.parse_identifier_or_enum_pattern(enum_name),
            TokenType::BoolLiteral(literal) => Ok(Pattern::BoolLiteralPattern(self.generate_random_variable(), literal)),
            TokenType::StrLiteral(literal) => Ok(Pattern::StrLiteralPattern(self.generate_random_variable(), literal)),
            TokenType::IntLiteral(literal) => self.parse_int_range_pattern(literal.try_into().unwrap()),
            TokenType::OpenParen => self.parse_tuple_pattern(),
            TokenType::OpenSquare => self.parse_array_pattern(),
            TokenType::DoubleDot => self.parse_leq_range_pattern(),
            _ => panic!("Did not expect {:?}", next_token)
        }
    }


    fn parse_leq_range_pattern(&mut self) -> Result<Pattern, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        let pattern_id = self.generate_random_variable();
        match next_token.token_type {
            TokenType::IntLiteral(literal) => Ok(Pattern::LessThanEqRangePattern(pattern_id, literal.try_into()?)),
            _ => Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Literal)))
        }
    }


    fn parse_int_range_pattern(&mut self, literal: i64) -> Result<Pattern, Box<dyn Error>> {
        let pattern_id = self.generate_random_variable();
        let next_token = self.tokens.front().unwrap();
        match next_token.token_type {
            TokenType::DoubleDot => {
                self.tokens.pop_front().unwrap();
                let next_token = self.tokens.front().unwrap();
                match next_token.token_type {
                    TokenType::IntLiteral(end_literal) => {
                        self.tokens.pop_front().unwrap();
                        Ok(Pattern::BetweenEqRangePattern(pattern_id, literal, end_literal.try_into().unwrap()))
                    }
                    _ => Ok(Pattern::GreaterThanEqRangePattern(pattern_id, literal))
                }
            }
            _ => Ok(Pattern::IntLiteralPattern(pattern_id, literal))
        }
    }


    fn parse_array_pattern(&mut self) -> Result<Pattern, Box<dyn Error>> {
        // return an empty array pattern if the list of subpatterns is empty
        if let TokenType::CloseSquare = self.tokens.front().unwrap().token_type {
            self.tokens.pop_front().unwrap();
            return Ok(Pattern::ArrayPattern(self.generate_random_variable(), vec![], Box::new(None)));
        }

        // get colon-separated patterns until a close square bracket is encountered
        let mut patterns: Vec<Pattern> = vec![];
        loop {
            patterns.push(self.parse_match_pattern()?);
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Colon => (),
                TokenType::CloseSquare => break,
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseSquare)))
            }
        }

        // if there is only 1 pattern, then don't try and split the pattern into a head and tail as
        // there is only a head
        if patterns.len() <= 1 {
            return Ok(Pattern::ArrayPattern(self.generate_random_variable(), patterns, Box::new(None)));
        }

        // if there is more than 1 subpattern, and the last subpattern is an identifier, then the
        // last subpattern is for the tail
        match &patterns.last().unwrap() {
            Pattern::IdentifierPattern(_) => {
                let last_pattern = patterns.pop().unwrap();
                Ok(Pattern::ArrayPattern(self.generate_random_variable(), patterns, Box::new(Some(last_pattern))))
            }
            _ => Ok(Pattern::ArrayPattern(self.generate_random_variable(), patterns, Box::new(None)))
        }
    }


    fn parse_tuple_pattern(&mut self) -> Result<Pattern, Box<dyn Error>> {
        let mut patterns: Vec<Pattern> = vec![];
        loop {
            patterns.push(self.parse_match_pattern()?);
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseParen => break,
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen)))
            }
        }

        Ok(Pattern::TuplePattern(self.generate_random_variable(), patterns))
    }


    fn parse_identifier_or_enum_pattern(&mut self, enum_name: String) -> Result<Pattern, Box<dyn Error>> {
        let next_token = self.tokens.front().unwrap();
        
        // check if this is an identifier pattern or an identifier pattern
        match next_token.token_type {
            TokenType::DoubleColon => self.tokens.pop_front(),
            _ => return Ok(Pattern::IdentifierPattern(enum_name))
        };

        let next_token = self.tokens.pop_front().unwrap();
        let variant_name = if let TokenType::Identifier(name) = next_token.token_type {
            name
        } else {
            panic!()
        };

        match self.tokens.front().unwrap().token_type {
            TokenType::ThickArrow => Ok(Pattern::EnumPattern(enum_name, variant_name, vec![])),
            TokenType::OpenParen => Ok(Pattern::EnumPattern(enum_name, variant_name, self.parse_enum_pattern_data_params()?)),
            _ => Err(Box::new(ParsingError::UnexpectedToken(self.tokens.front().unwrap().clone(), ExpectedToken::ThickArrow)))
        }
    }


    fn parse_enum_pattern_data_params(&mut self) -> Result<Vec<Pattern>, Box<dyn Error>> {
        let mut data_params: Vec<Pattern> = vec![];
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenParen);

        loop {
            data_params.push(self.parse_match_pattern()?);
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseParen => break,
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen)))
            }
        }

        Ok(data_params)
    }


    /// Parses a for loop which should conform to the EBNF:
    /// 
    /// `FOR_LOOP ::= "for" "(" <IDENTIFIER> ":" <TYPE> "in" <EXPRESSION> ")" "{" <BODY> "}"`
    fn parse_for_loop(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenParen);

        let next_token = self.tokens.pop_front().unwrap();
        let (iterator_line, iterator_col) = (next_token.line_number, next_token.col_number);
        let iterator_id: String = match next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier)))
        };

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Colon);

        let iterator_type = self.parse_type().unwrap();

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, InKeyword);

        let iterator_expr = self.parse_expression()?;
        let iterator_expr_type = get_expr_type(&iterator_expr, &self.current_symbol_table.borrow()).unwrap();
        if !iterator_type.is_compatible_with(&get_array_inner_type(&iterator_expr_type)) {
            panic!("Iterator variable type must be compatible with the type of the elements of the iterator expression!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseParen);
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenCurly);

        let iterator_symbol = Symbol::new(
            SymbolType::Variable(iterator_id.clone(), iterator_type.clone()), 
            iterator_line, iterator_col
        );
        let body = self.parse_stmt_block(vec![iterator_symbol])?;

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseCurly);

        Ok(SyntaxTree::new(SyntaxNode::ForStmt(iterator_id, iterator_type, Box::new(iterator_expr), Box::new(body)), line_num, col_num))
    }


    fn parse_func_call_or_reassignment_stmt(&mut self, id: String, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        let next_token = self.tokens.get(0).unwrap();
        match next_token.token_type {
            TokenType::OpenParen => self.parse_func_call_stmt(id, line_num, col_num),
            TokenType::Equal
            | TokenType::OpenSquare => self.parse_reassignment(id, line_num, col_num),
            _ => panic!()
        }
    }


    fn parse_reassignment(&mut self, id: String, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        match self.current_symbol_table.borrow().get(&id) {
            Some(_) => (),
            None => panic!("Semantic error: The identifier {} could not be found!", id)
        }

        let next_token = self.tokens.pop_front().unwrap();
        let lhs = match next_token.token_type {
            TokenType::Equal => SyntaxTree::new(SyntaxNode::Identifier(id.clone()), line_num, col_num),
            TokenType::OpenSquare => {
                let expr = self.parse_expression()?;

                let next_token = self.tokens.pop_front().unwrap();
                assert_token_type!(next_token, CloseSquare);

                let next_token = self.tokens.pop_front().unwrap();
                assert_token_type!(next_token, Equal);

                SyntaxTree::new(SyntaxNode::ArrayIndexingOperation(
                    Box::new(expr),
                    Box::new(SyntaxTree::new(SyntaxNode::Identifier(id.clone()), line_num, col_num))
                ), line_num, col_num)
            }

            other => panic!("Invalid left expression, found {:?}", other)
        };

        let expr = self.parse_expression()?;
        let expr_type: Type = get_expr_type(&expr, &self.current_symbol_table.borrow()).unwrap();
        let lhs_type: Type = get_l_expr_type(&lhs, &self.current_symbol_table.borrow()).unwrap();
        if !expr_type.is_compatible_with(&lhs_type) {
            panic!("Mismatch between variable and expression types!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Semicolon);

        Ok(SyntaxTree::new(SyntaxNode::ReassignmentStmt(Box::new(lhs), Box::new(expr), lhs_type), line_num, col_num))
    }


    /// Parses a let statement
    /// 
    /// Let statements have the form: `"let" <identifier> ":" <type> "=" <expression> ";"`.
    fn parse_let_statement(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        let id: String = match next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier)))
        };

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Colon);

        let var_type = self.parse_type().unwrap();

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Equal);

        let expression: SyntaxTree = self.parse_expression()?;
        let expr_type: Type = get_expr_type(&expression, &self.current_symbol_table.borrow()).unwrap();

        // if the type is an raw enum name and not an enum instantiation, it is not valid as it is
        // not a type
        match expr_type.basic_type {
            SimpleType::Enum(_, _, None) => panic!("A raw enum is a type, not a value!"),
            _ => ()
        }

        if !var_type.is_compatible_with(&expr_type) {
            panic!("Mismatch between variable and expression types on line {}, col {}!", expression.start_line, expression.start_index);
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Semicolon);

        self.current_symbol_table.borrow_mut().insert(Symbol::new(SymbolType::Variable(id.clone(), var_type.clone()), line_num, col_num));
        Ok(SyntaxTree::new(SyntaxNode::LetStmt(id, var_type, Box::new(expression)), line_num, col_num))
    }


    /// Parses a type from the current stream of tokens (excluding computational types)
    /// 
    /// Needs to support: 
    ///  - basic types,
    ///  - linear types,
    ///  - monadic types,
    ///  - structs,
    ///  - enums,
    ///  - tuples,
    ///  - generics
    fn parse_type(&mut self) -> Result<Type, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        let basic_type = match next_token.token_type {
            TokenType::Identifier(id) => id,
            TokenType::OpenParen => return self.parse_tuple_type(),
            _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier)))
        };

        // check if there is a generic component
        let generics: Vec<Type> = match self.tokens.get(0).unwrap().token_type {
            TokenType::LeftArrow => {
                self.tokens.pop_front().unwrap();

                let mut generic_types: Vec<Type> = vec![];
                while let Ok(t) = self.parse_type() {
                    generic_types.push(t);

                    let next_token = self.tokens.pop_front().unwrap();
                    match next_token.token_type {
                        TokenType::Comma => continue,
                        TokenType::RightArrow => break,
                        other => panic!("Expected , or >, got {:?}", other)
                    }
                }

                generic_types
            }

            _ => vec![] // no generic
        };

        let mut final_type: Type = Type::new_str(basic_type, false, generics, &self.current_symbol_table.borrow())?;

        loop {
            let next_token = self.tokens.get(0).unwrap();
            match &next_token.token_type {
                TokenType::OpenSquare => {
                    self.tokens.pop_front();
                    
                    let size_expr = self.parse_expression()?;
                    if !is_constexpr(&size_expr) {
                        panic!("Array index must be a constexpr!");
                    }

                    let size = fold_constexpr_index(&size_expr);
                    
                    let next_token = self.tokens.pop_front().unwrap();
                    if let TokenType::CloseSquare = next_token.token_type {
                        final_type = Type::new(SimpleType::Array(Box::new(final_type), size), false, vec![]);
                    } else {
                        return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseSquare)));
                    }
                },
                _ => break
            }
        }

        Ok(final_type)
    }


    /// Parses a tuple type, which is a parenthesized list of types separated by commas
    fn parse_tuple_type(&mut self) -> Result<Type, Box<dyn Error>> {
        let mut types: Vec<Type> = vec![];
        loop {
            types.push(self.parse_type()?);

            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseParen => break,
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen)))
            }
        }

        if types.len() < 2 {
            panic!("Tuple must have at least 2 elements!");
        }

        Ok(Type::new(SimpleType::Tuple(types), false, vec![]))
    }


    fn parse_while_loop(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenParen);

        let expr = self.parse_expression()?;
        if get_expr_type(&expr, &self.current_symbol_table.borrow()).unwrap() != Type::new(SimpleType::Bool, false, vec![]) {
            panic!("If statement's condition must be of type bool!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseParen);
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenCurly);

        let body = self.parse_stmt_block(vec![])?;

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseCurly);

        Ok(SyntaxTree::new(SyntaxNode::WhileStmt(Box::new(expr), Box::new(body)), line_num, col_num))
    }


    fn parse_func_call_stmt(&mut self, id: String, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        // check that the function exists in this context
        match self.current_symbol_table.borrow().get(&id).unwrap().category {
            SymbolType::Function(_, _) => (),
            _ => panic!("Identifier {} is not a valid function name in this context", id)
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenParen);

        let arguments: Vec<SyntaxTree> = self.parse_func_args()?;

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Semicolon);
        
        let expr = SyntaxTree::new(SyntaxNode::FunctionCallStmt(id, arguments), line_num, col_num);
        get_expr_type(&expr, &self.current_symbol_table.borrow()).unwrap();
        return Ok(expr);
    }


    fn parse_return(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        let expr = self.parse_expression()?;

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Semicolon);

        return Ok(SyntaxTree::new(SyntaxNode::ReturnStmt(Box::new(expr)), line_num, col_num));
    }


    /// Parses an expression, such as `x * 3 > 20`, including operators with operator precedence
    /// 
    /// Uses recursive descent with a separate rule for each level of precedence. Literals occupy
    /// the highest level of precedence and the `&&` operator occupies the lowest level of operator
    /// precedence.
    /// 
    /// # Examples
    /// 
    /// See [`Parser::parse_func_body()`] for examples of use.
    fn parse_expression(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        let left = self.parse_logical_or()?;
        let (left_line, left_col) = (left.start_line, left.start_index);
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::Question => {
                let true_expr: SyntaxTree = self.parse_expression()?;
                let next_token = self.tokens.pop_front().unwrap();
                assert_token_type!(next_token, Colon);

                let false_expr: SyntaxTree = self.parse_expression()?;
                return Ok(SyntaxTree::new(SyntaxNode::TernaryExpression(
                    Box::new(left), Box::new(true_expr), Box::new(false_expr)
                ), left_line, left_col));
            }

            _ => {
                self.tokens.push_front(next_token);
            }
        }

        Ok(left)
    }


    fn parse_logical_or(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_logical_and, DoublePipe => "||")
    }


    fn parse_logical_and(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_bitwise_xor, DoubleAmpersand => "&&")
    }
    
    
    fn parse_bitwise_xor(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_bitwise_or, UpArrow => "^")
    }


    fn parse_bitwise_or(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_bitwise_and, Pipe => "|")
    }


    fn parse_bitwise_and(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_equality, Ampersand => "&")
    }


    fn parse_equality(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_concatenation, DoubleEqual => "==", BangEqual => "!=")
    }
    
    
    // Could either be a concatenation or an enum instantiation
    fn parse_concatenation(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        let mut root: SyntaxTree = self.parse_scalar_comparisons()?;
        let (root_line, root_col) = (root.start_line, root.start_index);

        // if the root is an identifier, check if it is for an enum, in which case it must be an
        // enum instantiation and not a raw type name
        let root_type = match root.node.clone() {
            SyntaxNode::Identifier(id) => {
                let rt = get_expr_type(&root, &self.current_symbol_table.borrow()).unwrap();
                match rt.basic_type {
                    SimpleType::Enum(name, _, None) => {
                        match self.current_symbol_table.clone().borrow().get(&id).unwrap().category {
                            // is an enum name and must be am instantiation
                            SymbolType::EnumeraionType(_, _) => return self.parse_enum_instantiation(root, name),
                            // is not an enum name
                            _ => get_expr_type(&root, &self.current_symbol_table.borrow())?
                        }
                    },
                    _ => rt
                }
            }

            _ => get_expr_type(&root, &self.current_symbol_table.borrow())?
        };
        
        match root_type.basic_type.clone() {
            SimpleType::Enum(_, _, _) => Ok(root),
            _ => { // is an array concatenation
                loop {
                    let next_token = self.tokens.pop_front().unwrap();
                    match next_token.token_type {
                        TokenType::DoubleColon => {
                            let right: SyntaxTree = self.parse_scalar_comparisons()?;
                            root = SyntaxTree::new(SyntaxNode::BinaryOperation(
                                "::".to_owned(),
                                Box::new(root),
                                Box::new(right),
                            ), root_line, root_col);
                        }
        
                        // End of this level of precedence
                        _ => {
                            self.tokens.push_front(next_token);
                            break;
                        }
                    }
                }
        
                Ok(root)
            }
        }
    }


    fn parse_enum_instantiation(&mut self, root: SyntaxTree, name: String) -> Result<SyntaxTree, Box<dyn Error>> {
        let (root_line, root_col) = (root.start_line, root.start_index);
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, DoubleColon);

        let next_token = self.tokens.pop_front().unwrap();
        let variant_id = match next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier)))
        };

        let variant_params: IndexMap<String, SyntaxTree> = self.parse_enum_variant_params()?;
        let name_category = self.current_symbol_table.borrow().get(&name).unwrap().category;
        let enum_type = match &name_category {
            SymbolType::EnumeraionType(_, t) => t,
            _ => panic!()
        };

        match &enum_type.basic_type {
            SimpleType::Enum(_, variants, _) => {
                // check that the number of parameters passed to the variant matches the number of
                // parameters the variant has
                let enum_variant_params = variants.get(&variant_id).unwrap();
                assert_eq!(enum_variant_params.len(), variant_params.len());

                // check that the passed arguments have the correct type
                for (p_name, p_type) in enum_variant_params {
                    let variant_param_type = get_expr_type(
                        variant_params.get(p_name).unwrap(), 
                        &self.current_symbol_table.borrow()
                    )?;
                    
                    assert!(variant_param_type.is_compatible_with(p_type));
                }
            }
            _ => panic!()
        };

        Ok(SyntaxTree::new(
            SyntaxNode::EnumInstantiation(
                enum_type.clone(), 
                variant_id, 
                variant_params
            ), 
            root_line, root_col)
        )
    }


    fn parse_enum_variant_params(&mut self) -> Result<IndexMap<String, SyntaxTree>, Box<dyn Error>> {
        let mut variant_params: IndexMap<String, SyntaxTree> = IndexMap::new();
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::OpenParen => {
                loop {
                    // get the id of the argument
                    let next_token = self.tokens.pop_front().unwrap();
                    let arg_id = match next_token.token_type {
                        TokenType::Identifier(id) => id,
                        _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier)))
                    };

                    // assert the id is followed by a token
                    let next_token = self.tokens.pop_front().unwrap();
                    assert_token_type!(next_token, Colon);

                    // get the expression associated with this argument
                    let arg = self.parse_expression()?;
                    variant_params.insert(arg_id, arg);

                    // check if the list of arguments has ended or not
                    let next_token = self.tokens.pop_front().unwrap();
                    match next_token.token_type {
                        TokenType::CloseParen => break,
                        TokenType::Comma => continue,
                        _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen)))
                    }
                }

                Ok(variant_params)
            },
            _ => { // if there is no list of arguments, return an empty map
                self.tokens.push_front(next_token);
                Ok(IndexMap::new())
            } 
        }
    }


    fn parse_scalar_comparisons(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_shifts, RightArrow => ">", LeftArrow => "<", LeftArrowEqual => "<=", RightArrowEqual => ">=")
    }


    fn parse_shifts(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_plus_minus, DoubleRightArrow => ">>", TripleRightArrow => ">>>", DoubleLeftArrow => "<<")
    }


    fn parse_plus_minus(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_mult_div_modulo, Plus => "+", Minus => "-")
    }


    fn parse_mult_div_modulo(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_arrow, Star => "*", FwdSlash => "/", Percent => "%")
    }


    fn parse_arrow(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_right_assoc_unary, Arrow => "->")
    }


    fn parse_right_assoc_unary(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::Minus => Ok(SyntaxTree::new(SyntaxNode::RightAssocUnaryOperation(
                "-".to_owned(),
                Box::new(self.parse_right_assoc_unary()?),
            ), next_token.line_number, next_token.col_number)),

            TokenType::Plus => Ok(SyntaxTree::new(SyntaxNode::RightAssocUnaryOperation(
                "+".to_owned(),
                Box::new(self.parse_right_assoc_unary()?),
            ), next_token.line_number, next_token.col_number)),

            TokenType::Bang => Ok(SyntaxTree::new(SyntaxNode::RightAssocUnaryOperation(
                "!".to_owned(),
                Box::new(self.parse_right_assoc_unary()?),
            ), next_token.line_number, next_token.col_number)),

            TokenType::Complement => Ok(SyntaxTree::new(SyntaxNode::RightAssocUnaryOperation(
                "~".to_owned(),
                Box::new(self.parse_right_assoc_unary()?),
            ), next_token.line_number, next_token.col_number)),

            // End of this level of precedence
            _ => {
                self.tokens.push_front(next_token);
                self.parse_left_assoc_unary()
            }
        }
    }

    fn parse_left_assoc_unary(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        let mut root: SyntaxTree = self.parse_range().unwrap();
        loop {
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::DoublePlus => {
                    root = SyntaxTree::new(SyntaxNode::LeftAssocUnaryOperation(
                        "++".to_owned(),
                        Box::new(root),
                    ), next_token.line_number, next_token.col_number);
                }

                TokenType::DoubleMinus => {
                    root = SyntaxTree::new(SyntaxNode::LeftAssocUnaryOperation(
                        "--".to_owned(),
                        Box::new(root),
                    ), next_token.line_number, next_token.col_number);
                }

                TokenType::OpenSquare => {
                    let root_type: Type = get_expr_type(&root, &self.current_symbol_table.borrow()).unwrap();
                    let expr = self.parse_expression()?;

                    // check if the expression is an array range, which means it is actually a
                    // subarray instead
                    match &expr.node {
                        SyntaxNode::BinaryOperation(op, l, r) => {
                            if op.as_str() == ".." {
                                assert!(is_constexpr(&l));
                                assert!(is_constexpr(&r));
                                let start = fold_constexpr_index(&l);
                                let end = fold_constexpr_index(&r);
                                root = SyntaxTree::new(SyntaxNode::SubarrayOperation(
                                    Box::new(root), root_type.clone(), start, end
                                ), expr.start_line, expr.start_index);

                                let next_token = self.tokens.pop_front().unwrap();
                                assert_token_type!(next_token, CloseSquare);
                                continue;
                            }
                        }

                        _ => ()
                    }

                    // this is an indexing operation
                    let next_token = self.tokens.pop_front().unwrap();
                    assert_token_type!(next_token, CloseSquare);
                    root = match root_type.basic_type {
                        SimpleType::Tuple(_) => SyntaxTree::new(
                            SyntaxNode::TupleIndexingOperation(
                                Box::new(expr), 
                                Box::new(root)
                            ), next_token.line_number, next_token.col_number
                        ),
                        SimpleType::Array(_, _) => SyntaxTree::new(
                            SyntaxNode::ArrayIndexingOperation(
                                Box::new(expr), 
                                Box::new(root)
                            ), next_token.line_number, next_token.col_number
                        ),
                        _ => panic!("Expected tuple or array!")
                    };
                }

                // End of this level of precedence
                _ => {
                    self.tokens.push_front(next_token);
                    break;
                }
            }
        }

        Ok(root)
    }


    fn parse_range(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_factor, DoubleDot => "..")
    }


    /// Parses a factor, which is a literal, function invocation, or parenthesized expression.
    fn parse_factor(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::StrLiteral(s) => Ok(SyntaxTree::new(SyntaxNode::StringLiteral(s), next_token.line_number, next_token.col_number)),
            TokenType::IntLiteral(n) => Ok(SyntaxTree::new(SyntaxNode::IntLiteral(n), next_token.line_number, next_token.col_number)),
            TokenType::BoolLiteral(b) => Ok(SyntaxTree::new(SyntaxNode::BoolLiteral(b), next_token.line_number, next_token.col_number)),
            TokenType::DoKeyword => self.parse_do_block(),

            TokenType::Identifier(id) => {
                // check that the identifier is valid in this context
                match self.current_symbol_table.borrow().get(&id) {
                    Some(_) => (),
                    None => panic!("Semantic error: The identifier {} could not be found on line {}, col {}!", id, next_token.line_number, next_token.col_number)
                }

                let func_call_paren = self.tokens.pop_front().unwrap();
                match func_call_paren.token_type {
                    TokenType::OpenParen => { // function call
                        let arguments: Vec<SyntaxTree> = self.parse_func_args()?;
                        return Ok(SyntaxTree::new(SyntaxNode::FunctionCall(id, arguments), func_call_paren.line_number, func_call_paren.col_number));
                    }

                    _ => {
                        self.tokens.push_front(func_call_paren);
                        return Ok(SyntaxTree::new(SyntaxNode::Identifier(id), next_token.line_number, next_token.col_number));
                    }
                }
            }

            TokenType::OpenParen => self.parse_tuple_or_paren_expr(),
            TokenType::OpenSquare => self.parse_array_literal(next_token.line_number, next_token.col_number),
            _ => Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Expression)))
        }
    }


    fn parse_array_literal(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        let mut elems: Vec<SyntaxTree> = vec![];
        loop {
            elems.push(self.parse_expression()?);
            let next_token = self.tokens.pop_front().unwrap();
            match &next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseSquare => break,
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseSquare)))
            } 
        }

        let inner_type = get_expr_type(elems.get(0).unwrap(), &self.current_symbol_table.borrow())?;
        Ok(SyntaxTree::new(SyntaxNode::ArrayLiteral(elems, inner_type), line_num, col_num))
    } 


    /// Used when it is unclear if the next set of tokens represents a parenthesized expression or
    /// a tuple. This can be determined by seeing if the first expression encountered ends with a
    /// comma, making it a tuple, or a close parenthesis, making it a parenthesized expression.
    fn parse_tuple_or_paren_expr(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        let expr = self.parse_expression()?;
        let next_token = self.tokens.pop_front().unwrap();
        match &next_token.token_type {
            TokenType::CloseParen => Ok(SyntaxTree::new(SyntaxNode::ParenExpr(Box::new(expr)), next_token.line_number, next_token.col_number)),
            TokenType::Comma => self.parse_tuple(expr, next_token.line_number, next_token.col_number),
            _ => panic!()
        }
    }


    /// Parses a tuple, which syntactically is a comma-separated list of 2 or more expressions, the
    /// whole thing of which is enclosed in parentheses.
    fn parse_tuple(&mut self, first_expr: SyntaxTree, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        let mut expressions: Vec<SyntaxTree> = vec![first_expr];
        loop {
            expressions.push(self.parse_expression()?);
            let next_token = self.tokens.pop_front().unwrap();
            match &next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseParen => break,
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen)))
            } 
        }

        Ok(SyntaxTree::new(SyntaxNode::TupleLiteral(expressions), line_num, col_num))
    }


    /// Produces a monadic action such as `IO<()>` or `IO<str>`.
    /// 
    /// The value contained within a monad cannot be extracted from a monad outside of another
    /// monad, as in Haskell, for example. This ensures that side effects, such as reading and
    /// writing from standard I/O, are properly ordered and are not parallelized, causing problems
    /// with out-of-order effects - this is why monads are never parallelized.
    fn parse_do_block(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        let (line, col) = (next_token.line_number, next_token.col_number);
        assert_token_type!(next_token, OpenCurly);

        let body = self.parse_stmt_block(vec![])?;

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseCurly);

        Ok(SyntaxTree::new(SyntaxNode::MonadicExpr(Box::new(body)), line, col))
    }


    fn parse_func_args(&mut self) -> Result<Vec<SyntaxTree>, Box<dyn Error>> {
        let mut args: Vec<SyntaxTree> = vec![];
        let next_token = self.tokens.pop_front().unwrap();
        // return an empty vec if there are no arguments
        if let TokenType::CloseParen = next_token.token_type {
            return Ok(vec![]);
        }

        // put token back so it can be included in the first argument's expression
        self.tokens.push_front(next_token);

        // get all the arguments into the vec (which are comma separated) until the last ")" token 
        // is reached
        loop {
            args.push(self.parse_expression()?);
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::CloseParen => break,
                TokenType::Comma => continue,
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen)))
            }
        }

        Ok(args)
    }


    fn parse_selection(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        // parse the condition
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenParen);

        let cond = self.parse_expression()?;
        if get_expr_type(&cond, &self.current_symbol_table.borrow()).unwrap() != Type::new(SimpleType::Bool, false, vec![]) {
            panic!("If statement's condition must be of type bool!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseParen);

        let next_token = self.tokens.pop_front().unwrap();
        let if_body = match next_token.token_type {
            TokenType::OpenCurly => {
                let result = self.parse_stmt_block(vec![])?;
                let next_token = self.tokens.pop_front().unwrap();
                assert_token_type!(next_token, CloseCurly);
                result
            },

            _ => {
                self.tokens.push_front(next_token);
                self.parse_statement()?
            }
        };

        let next_token = self.tokens.pop_front().unwrap();
        let else_body = match next_token.token_type {
            TokenType::ElseKeyword => {
                let next_token = self.tokens.pop_front().unwrap();
                Some(match next_token.token_type {
                    TokenType::OpenCurly => {
                        let result = self.parse_stmt_block(vec![])?;
                        let next_token = self.tokens.pop_front().unwrap();
                        assert_token_type!(next_token, CloseCurly);
                        result
                    },

                    _ => {
                        self.tokens.push_front(next_token);
                        self.parse_statement()?
                    }
                })
            },

            _ => {
                self.tokens.push_front(next_token);
                None
            }
        };

        Ok(SyntaxTree::new(SyntaxNode::SelectionStatement(Box::new(cond), Box::new(if_body), Box::new(else_body)), line_num, col_num))
    }


    fn get_enum_variants_data(&self, variants: &Vec<SyntaxTree>) -> IndexMap<String, IndexMap<String, Type>> {
        let mut result: IndexMap<String, IndexMap<String, Type>> = IndexMap::new();
        for variant in variants {
            match &variant.node {
                SyntaxNode::EnumVariant(name, params) => result.insert(name.to_string(), params.clone()),
                _ => panic!()
            };
        }

        result
    }


    fn parse_enumeration(&mut self, start_line: usize, start_index: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        let identifier = match next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier)))
        };

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Equal);

        let variants = self.parse_enum_variants()?;
        let variant_data = self.get_enum_variants_data(&variants);

        let t: Type = Type::from_basic(SimpleType::Enum(identifier.clone(), variant_data, None));
        self.current_symbol_table.borrow_mut().insert(
            Symbol::new(SymbolType::EnumeraionType(identifier.clone(), t.clone()), 
            start_line, start_index)
        );
        Ok(SyntaxTree::new(SyntaxNode::Enumeraion(identifier, variants), start_line, start_index))
    }


    fn parse_enum_variants(&mut self) -> Result<Vec<SyntaxTree>, Box<dyn Error>> {
        let mut variants: Vec<SyntaxTree> = vec![];
        variants.push(self.parse_enum_variant()?);

        loop {
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Pipe => variants.push(self.parse_enum_variant()?),
                TokenType::Semicolon => break,
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Semicolon)))
            }
        }

        Ok(variants)
    }


    fn parse_enum_variant(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        // get the enum variant name
        let next_token = self.tokens.pop_front().unwrap();
        let identifier = match next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier)))
        };

        let next_token = self.tokens.pop_front().unwrap();
        let params: IndexMap<String, Type> = match next_token.token_type {
            TokenType::OpenParen => {
                let mut params: IndexMap<String, Type> = IndexMap::new();
                // loop collecting the parameters of the variant (if any)
                loop {
                    // gets the id of the parameter and the parameter's type, and adds it to params
                    let next_token = self.tokens.pop_front().unwrap();
                    match next_token.token_type {
                        TokenType::Identifier(param_id) => {
                            let next_token = self.tokens.pop_front().unwrap();
                            assert_token_type!(next_token, Colon);
                            let param_type = self.parse_type()?;
                            params.insert(param_id, param_type);
                        },
                        _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier)))
                    }

                    // end the loop if it is the end of the params list, or continue if there is
                    // another parameter
                    let next_token = self.tokens.pop_front().unwrap();
                    match next_token.token_type {
                        TokenType::CloseParen => break,
                        TokenType::Comma => continue,
                        _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen)))
                    }
                }

                params
            }

            _ => {
                self.tokens.push_front(next_token.clone());
                IndexMap::new()
            }
        };

        Ok(SyntaxTree::new(
            SyntaxNode::EnumVariant(identifier, params), 
            next_token.line_number, next_token.col_number
        ))
    }
}
