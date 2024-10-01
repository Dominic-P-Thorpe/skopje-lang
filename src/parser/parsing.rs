use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

use indexmap::IndexMap;
use rand::distributions::{Alphanumeric, DistString};

use crate::semantics::computational_types::calculate_computational_dependencies;
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
            let next_token = match $self.tokens.pop_front() {
                Some(token) => token,
                None => return Err(ParsingError::EarlyReturn(root))
            };

            match next_token.token_type {
                $(
                    TokenType::$op_type => {
                        let right: SyntaxTree = match $self.$next() {
                            Err(e) => match e {
                                ParsingError::EarlyReturn(t) => t,   
                                e => return Err(e)
                            },
                            Ok(t) => t
                        };

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
            _ => return Err(ParsingError::UnexpectedToken($token, ExpectedToken::$token_type))
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
    FloatLiteralPattern(String, f64),
    StrLiteralPattern(String, String),
    BoolLiteralPattern(String, bool)
}


#[derive(Debug, Clone, PartialEq)]
pub enum SyntaxNode {
    Program(Box<SyntaxTree>),
    /// name, variants
    Enumeraion(String, Vec<SyntaxTree>, HashMap<String, SyntaxTree>),
    /// name, parameters (param name, param type)
    EnumVariant(String, IndexMap<String, Type>),
    /// Enum type, variant name, variant arguments
    EnumInstantiation(Type, String, IndexMap<String, SyntaxTree>),
    /// Struct name and members
    Struct(String, IndexMap<String, Type>, HashMap<String, SyntaxTree>),
    /// struct name and members
    StructInstantiation(String, IndexMap<String, SyntaxTree>),
    /// function name, arguments (id, type), return type, body statements
    Function(String, Vec<(String, Type)>, Type, Box<SyntaxTree>),
    /// expression to return
    ReturnStmt(Box<SyntaxTree>),
    /// condition, body
    WhileStmt(Box<SyntaxTree>, Box<SyntaxTree>),
    /// Loop variable name, loop var type, expr to loop over, loop body
    ForStmt(String, Type, Box<SyntaxTree>, Box<SyntaxTree>),
    BreakStmt,
    ContinueStmt,
    /// expression to match, patterns to match against and syntax tree to run if match succeeds,
    /// type of the expression to match
    /// Members of vector of patterns are a tuple where the first element is a vector of patterns
    /// and the second is the body to run if any of those patterns are a match
    MatchStmt(Box<SyntaxTree>, Vec<(Pattern, SyntaxTree)>, Type),
    /// variable name, type, expression
    LetStmt(String, Type, Box<SyntaxTree>),
    /// variable name, new value expression, type of the variable being reassigned
    /// type is needed so that is can be used when generating the C++ code
    ReassignmentStmt(Box<SyntaxTree>, Box<SyntaxTree>, Type),
    /// condition, body, optional else
    SelectionStatement(Box<SyntaxTree>, Box<SyntaxTree>, Box<Option<SyntaxTree>>),
    /// binary operation, left side, right side
    BinaryOperation(String, Box<SyntaxTree>, Box<SyntaxTree>),
    RightAssocUnaryOperation(String, Box<SyntaxTree>),
    LeftAssocUnaryOperation(String, Box<SyntaxTree>),
    /// target type, source type, expression to cast
    TypeCast(Type, Type, Box<SyntaxTree>),
    TupleIndexingOperation(Box<SyntaxTree>, Box<SyntaxTree>),
    /// index to get, stmt to index
    ArrayIndexingOperation(Box<SyntaxTree>, Box<SyntaxTree>),
    /// array to get subarray of, type of original array, start index, end index
    SubarrayOperation(Box<SyntaxTree>, Type, usize, usize),
    ConcatStr(Box<SyntaxTree>, Box<SyntaxTree>),
    /// condition, value if true, value if false
    TernaryExpression(Box<SyntaxTree>, Box<SyntaxTree>, Box<SyntaxTree>),
    ParenExpr(Box<SyntaxTree>),
    /// body of the monad, its parameter, and its return type
    MonadicExpr(Box<SyntaxTree>, Option<(String, Type)>, Type),
    /// function name, arguments
    FunctionCall(String, Vec<SyntaxTree>),
    StringLiteral(String),
    IntLiteral(u64),
    FloatLiteral(f64),
    BoolLiteral(bool),
    TupleLiteral(Vec<SyntaxTree>),
    ArrayLiteral(Vec<SyntaxTree>, Type),
    /// store the type so that if the type is an std::unique_ptr we know to use std::move when we 
    /// want to use it
    Identifier(String),
    SelfIdentifier,
    /// a block of statements represented as a vec, and a pointer to the symbol table of that block
    StmtBlock(Vec<SyntaxTree>, Rc<RefCell<SymbolTable>>)
}


#[derive(Debug, Clone, PartialEq)]
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
    pub current_return_type: Option<Type>,
    symbol_table_root: Rc<RefCell<SymbolTable>>,
    current_symbol_table: Rc<RefCell<SymbolTable>>,
    auxilliary_var_index: usize,
    in_monad: bool
}


impl Parser {
    /// Creates a [`VecDeque`] of tokens which can be used as a FIFO queue data structure in the
    /// [`Parser`] struct.  
    pub fn new(tokens: Vec<Token>, symbol_table: Option<Rc<RefCell<SymbolTable>>>) -> Self {
        let symbol_table_root = symbol_table.unwrap_or(SymbolTable::new(None));
        Parser { 
            tokens: VecDeque::from(tokens),
            symbol_table_root: symbol_table_root.clone(),
            current_symbol_table: symbol_table_root,
            auxilliary_var_index: 0,
            current_return_type: None,
            in_monad: false
        }
    }


    pub fn parse(&mut self) -> Result<SyntaxTree, ParsingError> {
        let mut top_level_constructs: Vec<SyntaxTree> = vec![];
        while let Some(next_token) = self.tokens.pop_front() {
            match &next_token.token_type {
                TokenType::FnKeyword => top_level_constructs.push(self.parse_function(next_token.line_number, next_token.col_number)?),
                TokenType::EnumKeyword => top_level_constructs.push(self.parse_enumeration(next_token.line_number, next_token.col_number)?),
                TokenType::StructKeyword => top_level_constructs.push(self.parse_struct(next_token.line_number, next_token.col_number)?),
                other => panic!("Expected 'fn', 'enum', 'struct', or 'impl', got {:?}", other)
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


    /// Parses a struct definition from the token stream.
    ///
    /// This function expects to find an identifier representing the struct's name,
    /// followed by an open curly brace `{`, a list of members (each consisting of a name 
    /// and a type, separated by a colon), and a closing curly brace `}`. The members of 
    /// the struct are stored in a `HashMap` where the key is the member name and the value 
    /// is the member type.
    ///
    /// # Arguments
    ///
    /// * `line_num` - The current line number in the source code where the struct is defined.
    /// * `col_num` - The current column number in the source code.
    ///
    /// # Returns
    ///
    /// A `Result` that, on success, contains a `SyntaxTree` representing the parsed struct.
    /// If the parsing fails, an error is returned.
    ///
    /// # Errors
    ///
    /// * Returns an error if an unexpected token is encountered, such as when the expected 
    ///   identifier, open curly brace, comma, or closing curly brace is missing.
    fn parse_struct(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        // get the identifier of the struct
        let id_token = self.tokens.pop_front().unwrap();
        let name: String = match id_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(ParsingError::UnexpectedToken(id_token, ExpectedToken::Identifier))
        };

        // ensure the identifier is followed by a {
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenCurly);

        // get the first member of the struct, also ensures the struct has at least 1 member
        let mut members: IndexMap<String, Type> = IndexMap::new();
        let first_member = self.parse_struct_member()?;
        members.insert(first_member.0, first_member.1);

        // loop until we get to a }, parsing struct members on the way
        loop {
            let next_token: Token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Comma => (), // there are more members
                TokenType::CloseCurly => break, // this is the end of the declaration
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseCurly))
            }

            // get the new member
            let member = self.parse_struct_member()?;
            members.insert(member.0, member.1);
        }

        // create a new frame in the symbol table and set the current symbol tableto the new one
        let old_symbol_table = self.current_symbol_table.clone();
        self.current_symbol_table = SymbolTable::add_child(&self.current_symbol_table);

        // create a new symbol for the new struct, call it self as that is how it will be referred
        // to in the definition context, and add it to the symbol table
        let self_symbol = Symbol::new(SymbolType::StructType(String::from("self"), 
            Type::from_basic(SimpleType::Struct(name.clone(), members.clone(), HashMap::new()))
        ), false, id_token.line_number, id_token.col_number);
        self.current_symbol_table.borrow_mut().insert(self_symbol);
        
        // get the methods associated with the struct (if any)
        let next_token: &Token = self.tokens.front().unwrap();
        let methods: HashMap<String, SyntaxTree> = match next_token.token_type {
            TokenType::WithKeyword => {
                self.tokens.pop_front();
                self.parse_methods()?
            }
            _ => HashMap::new()
        };

        // restore the old symbol table now that we are done with the struct definition context
        self.current_symbol_table = old_symbol_table.clone();

        // get the type signatures of the methods and use them to construct the final struct types
        let method_types: HashMap<String, Box<Type>> = methods.iter()
                                                              .map(|(k, v)| (k.clone(), Box::new(get_function_type(v))))
                                                              .collect();
        let struct_type: Type = Type::from_basic(SimpleType::Struct(name.clone(), members.clone(), method_types));
        self.symbol_table_root.borrow_mut().insert(
            Symbol::new(SymbolType::StructType(name.clone(), struct_type), false, line_num, col_num)
        );
        Ok(SyntaxTree::new(SyntaxNode::Struct(name, members, methods), line_num, col_num))
    }


    fn parse_methods(&mut self) -> Result<HashMap<String, SyntaxTree>, ParsingError> {
        let mut methods: HashMap<String, SyntaxTree> = HashMap::new();

        let next_token: Token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenCurly);

        loop {
            let next_token: Token = self.tokens.pop_front().unwrap();
            let next_function = match next_token.token_type {
                TokenType::FnKeyword => self.parse_function(next_token.line_number, next_token.col_number)?,
                TokenType::CloseCurly => break,
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseCurly))
            };

            match &next_function.node {
                SyntaxNode::Function(name, _, _, _) => {
                    methods.insert(name.to_owned(), next_function.clone());
                    let func_type: Type = get_function_type(&next_function);
                    let mut self_type = self.current_symbol_table.borrow_mut()
                                             .get(&String::from("self")).unwrap()
                                             .get_type();
                    self_type.basic_type.add_behaviour(name.to_string(), func_type);
                    let struct_symbol = Symbol::new(SymbolType::StructType(String::from("self"), self_type), false, 0, 0);
                    self.current_symbol_table.borrow_mut().insert(struct_symbol);
                }
                _ => panic!()
            }
        }
        
        Ok(methods)
    }


    /// Parses a single member of a struct, which consists of an identifier followed by a colon and 
    /// a type.
    ///
    /// # Returns
    ///
    /// A `Result` that, on success, contains a tuple of the member's name (as a `String`) 
    /// and its type (as a `Type`).
    /// If the parsing fails, an error is returned.
    ///
    /// # Errors
    ///
    /// * Returns an error if an unexpected token is encountered, such as when the expected 
    ///   identifier or colon is missing.
    fn parse_struct_member(&mut self) -> Result<(String, Type), ParsingError> {
        // get the identifier of this member
        let id_token = self.tokens.pop_front().unwrap();
        let name: String = match id_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(ParsingError::UnexpectedToken(id_token, ExpectedToken::Identifier))
        };

        // ensure the next token is a :
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Colon);

        // get the type of the member
        let member_type = self.parse_type()?;
        Ok((name, member_type))
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
    fn parse_function(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        let id_token = self.tokens.pop_front().unwrap();
        if let TokenType::Identifier(id) = id_token.token_type {
            let open_paren = self.tokens.pop_front().unwrap();
            assert_token_type!(open_paren, OpenParen);

            let params: Vec<(String, Type)> = self.parse_func_params()?;

            let arrow = self.tokens.pop_front().unwrap();
            assert_token_type!(arrow, Arrow);

            let return_type = self.parse_type().unwrap();
            self.current_return_type = Some(return_type.clone());

            let open_body = self.tokens.pop_front().unwrap();
            assert_token_type!(open_body, OpenCurly);
            
            let body = self.parse_stmt_block(vec![])?;
            
            let close_body = self.tokens.pop_front().unwrap();
            assert_token_type!(close_body, CloseCurly);
            
            // add this function to the valid functions available in this context
            let func_type = Type::new(SimpleType::Function(
                Box::new(return_type.clone()), params.iter().map(|(_, t)| t).cloned().collect::<Vec<Type>>()
            ), false, vec![]);
            self.current_symbol_table.borrow_mut().insert(Symbol::new(SymbolType::Function(id.clone(), func_type), false, line_num, col_num));
            return Ok(SyntaxTree::new(
                SyntaxNode::Function(id, params, return_type, Box::new(body)), line_num, col_num
            ));
        }

        Err(ParsingError::UnexpectedToken(id_token, super::errors::ExpectedToken::Identifier))
    }


    fn parse_func_params(&mut self) -> Result<Vec<(String, Type)>, ParsingError> {
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
                return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier));
            };

            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Colon => (),
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Colon))
            }

            // TODO: make this work with all param types
            let p_type: Type = self.parse_type().unwrap();

            params.push((p_id.clone(), p_type.clone()));
            self.current_symbol_table.borrow_mut().insert(Symbol::new(SymbolType::Variable(p_id, p_type, vec![]), false, p_line, p_col));

            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::CloseParen => break,
                TokenType::Comma => continue,
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen))
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
    fn parse_stmt_block(&mut self, new_symbols: Vec<Symbol>) -> Result<SyntaxTree, ParsingError> {
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

        let new_symbol_table = self.current_symbol_table.clone();
        let parent_symbol_table = self.current_symbol_table.borrow()
                                      .parent.as_ref().unwrap()
                                      .upgrade().unwrap();
        self.current_symbol_table = parent_symbol_table;
        Ok(SyntaxTree::new(
            SyntaxNode::StmtBlock(statements, new_symbol_table), 
            start_line, start_index
        ))
    }


    fn parse_statement(&mut self) -> Result<SyntaxTree, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::ReturnKeyword => self.parse_return(next_token.line_number, next_token.col_number),
            TokenType::IfKeyword => self.parse_selection(next_token.line_number, next_token.col_number),
            TokenType::WhileKeyword => self.parse_while_loop(next_token.line_number, next_token.col_number),
            TokenType::Identifier(id) => self.parse_func_call_or_reassignment_stmt(id, next_token.line_number, next_token.col_number),
            TokenType::LetKeyword => self.parse_let_statement(next_token.line_number, next_token.col_number),
            TokenType::ForKeyword => self.parse_for_loop(next_token.line_number, next_token.col_number),
            TokenType::MatchKeyword => self.parse_match_stmt(next_token.line_number, next_token.col_number),
            TokenType::ContinueKeyword => {
                let next_token = self.tokens.pop_front().unwrap();
                assert_token_type!(next_token, Semicolon);
                Ok(SyntaxTree::new(SyntaxNode::ContinueStmt, next_token.line_number, next_token.col_number))
            }
            TokenType::BreakKeyword => {
                let next_token = self.tokens.pop_front().unwrap();
                assert_token_type!(next_token, Semicolon);
                Ok(SyntaxTree::new(SyntaxNode::BreakStmt, next_token.line_number, next_token.col_number))
            }
            _ => Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Statement))
        }
    }


    fn parse_match_stmt(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        // let match_expr = self.parse_expression()?;
        let next_token = self.tokens.pop_front().unwrap();
        let match_expr = match next_token.token_type {
            TokenType::Identifier(id) => SyntaxTree::new(SyntaxNode::Identifier(id), next_token.line_number, next_token.col_number),
            TokenType::SelfKeyword => SyntaxTree::new(SyntaxNode::SelfIdentifier, next_token.line_number, next_token.col_number),
            _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
        };

        let match_expr_type = get_expr_type(&match_expr, &self.current_symbol_table.borrow()).unwrap();

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


    fn parse_match_patterns(&mut self, match_expr_type: &Type) -> Result<Vec<(Pattern, SyntaxTree)>, ParsingError> {
        let mut patterns: Vec<(Pattern, SyntaxTree)> = vec![];
        loop {
            let next_token = self.tokens.front().unwrap();
            let (line_num, col_num) = (next_token.line_number, next_token.col_number);
            let sub_patterns: Vec<Pattern> = self.get_sub_patterns()?;
            
            let next_token = self.tokens.pop_front().unwrap();
            assert_token_type!(next_token, OpenCurly);

            let new_symbols: Vec<Symbol> = self.get_subpattern_symbols(&sub_patterns, match_expr_type, line_num, col_num)?;

            let statement_block: SyntaxTree = self.parse_stmt_block(new_symbols)?;

            let next_token = self.tokens.pop_front().unwrap();
            assert_token_type!(next_token, CloseCurly);

            for p in sub_patterns {
                patterns.push((p, statement_block.clone()));
            }

            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseCurly => break,
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseCurly))
            }
        }

        Ok(patterns)
    }


    fn get_sub_patterns(&mut self) -> Result<Vec<Pattern>, ParsingError> {
        let mut sub_patterns: Vec<Pattern> = vec![];
        loop {
            sub_patterns.push(self.parse_match_pattern()?);
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Pipe => continue,
                TokenType::ThickArrow => break,
                _ => return Err(ParsingError::UnexpectedToken(next_token.clone(), ExpectedToken::ThickArrow))
            }
        }

        Ok(sub_patterns)
    }


    fn get_subpattern_symbols(
        &mut self, 
        patterns: &Vec<Pattern>, 
        match_expr_type: &Type, 
        line_num: usize, 
        col_num: usize
    ) -> Result<Vec<Symbol>, ParsingError> {
        if patterns.len() == 0 {
            return Ok(vec![]);
        }

        let symbols = self.get_pattern_symbols(patterns.first().unwrap(), match_expr_type, line_num, col_num);
        for pattern in patterns {
            assert_eq!(symbols, self.get_pattern_symbols(&pattern, match_expr_type, line_num, col_num));
        }

        Ok(symbols)
    }


    fn get_pattern_symbols(&mut self, pattern: &Pattern, match_expr_type: &Type, line_num: usize, col_num: usize) -> Vec<Symbol> {
        match &pattern {
            Pattern::EnumPattern(enum_name, variant_name, _) => {
                let enum_type: Type = self.current_symbol_table.borrow().get(enum_name).unwrap().get_type();
                let expected_params = match &enum_type.basic_type {
                    SimpleType::Enum(_, variants, _, _, _) => 
                        variants.get(variant_name).unwrap(),
                    _ => panic!()
                };

                let data_params = self.get_data_params_from_enum_pattern(&pattern, &enum_type, variant_name, line_num, col_num);
                assert_eq!(data_params.len(), expected_params.len());
                data_params
            }

            Pattern::IdentifierPattern(id) => 
                vec![Symbol::new(SymbolType::Variable(id.to_owned(), match_expr_type.clone(), vec![]), false, line_num, col_num)],
            
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
                            new_symbols.push(Symbol::new(SymbolType::Variable(id.to_string(), member_type.clone(), vec![]), false, line_num, col_num)),
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
                            new_symbols.push(Symbol::new(SymbolType::Variable(id.to_string(), member_type.clone(), vec![]), false, line_num, col_num)),
                        _ => ()
                    }
                }

                match &**end {
                    None => (),
                    Some(p) => match p {
                        Pattern::IdentifierPattern(id) => 
                            new_symbols.push(Symbol::new(SymbolType::Variable(id.to_string(), member_type.clone(), vec![]), false, line_num, col_num)),
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
            SimpleType::Enum(_, variants, _, _, _) => variants.get(variant_name).unwrap(),
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
                        SymbolType::Variable(param_name.to_string(), param_type.clone(), vec![]), 
                        false, line_num, col_num)
                    );
                }
            }

            _ => panic!()
        }

        result
    }


    fn parse_match_pattern(&mut self) -> Result<Pattern, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::Identifier(enum_name) => self.parse_identifier_or_enum_pattern(enum_name),
            TokenType::BoolLiteral(literal) => Ok(Pattern::BoolLiteralPattern(self.generate_random_variable(), literal)),
            TokenType::StrLiteral(literal) => Ok(Pattern::StrLiteralPattern(self.generate_random_variable(), literal)),
            TokenType::IntLiteral(literal) => self.parse_int_range_pattern(literal.try_into().unwrap()),
            TokenType::FloatLiteral(literal) => Ok(Pattern::FloatLiteralPattern(self.generate_random_variable(), literal)),
            TokenType::SelfKeyword => self.parse_identifier_or_enum_pattern("self".to_owned()),
            TokenType::OpenParen => self.parse_tuple_pattern(),
            TokenType::OpenSquare => self.parse_array_pattern(),
            TokenType::DoubleDot => self.parse_leq_range_pattern(),
            _ => panic!("Did not expect {:?}", next_token)
        }
    }


    fn parse_leq_range_pattern(&mut self) -> Result<Pattern, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        let pattern_id = self.generate_random_variable();
        match next_token.token_type {
            TokenType::IntLiteral(literal) => Ok(Pattern::LessThanEqRangePattern(pattern_id, literal.try_into().unwrap())),
            _ => Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Literal))
        }
    }


    fn parse_int_range_pattern(&mut self, literal: i64) -> Result<Pattern, ParsingError> {
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


    fn parse_array_pattern(&mut self) -> Result<Pattern, ParsingError> {
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
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseSquare))
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


    fn parse_tuple_pattern(&mut self) -> Result<Pattern, ParsingError> {
        let mut patterns: Vec<Pattern> = vec![];
        loop {
            patterns.push(self.parse_match_pattern()?);
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseParen => break,
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen))
            }
        }

        Ok(Pattern::TuplePattern(self.generate_random_variable(), patterns))
    }


    fn parse_identifier_or_enum_pattern(&mut self, enum_name: String) -> Result<Pattern, ParsingError> {
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
            _ => Err(ParsingError::UnexpectedToken(self.tokens.front().unwrap().clone(), ExpectedToken::ThickArrow))
        }
    }


    fn parse_enum_pattern_data_params(&mut self) -> Result<Vec<Pattern>, ParsingError> {
        let mut data_params: Vec<Pattern> = vec![];
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenParen);

        loop {
            data_params.push(self.parse_match_pattern()?);
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseParen => break,
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen))
            }
        }

        Ok(data_params)
    }


    /// Parses a for loop which should conform to the EBNF:
    /// 
    /// `FOR_LOOP ::= "for" "(" <IDENTIFIER> ":" <TYPE> "in" <EXPRESSION> ")" "{" <BODY> "}"`
    fn parse_for_loop(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenParen);

        let next_token = self.tokens.pop_front().unwrap();
        let (iterator_line, iterator_col) = (next_token.line_number, next_token.col_number);
        let iterator_id: String = match next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
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
            SymbolType::Variable(iterator_id.clone(), iterator_type.clone(), vec![]), 
            false, iterator_line, iterator_col
        );
        let body = self.parse_stmt_block(vec![iterator_symbol])?;

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseCurly);

        Ok(SyntaxTree::new(SyntaxNode::ForStmt(iterator_id, iterator_type, Box::new(iterator_expr), Box::new(body)), line_num, col_num))
    }


    fn parse_func_call_or_reassignment_stmt(&mut self, id: String, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        let next_token = self.tokens.get(0).unwrap();
        match &next_token.token_type {
            TokenType::OpenParen => self.parse_func_call_stmt(id, line_num, col_num),
            TokenType::Equal
            | TokenType::OpenSquare => self.parse_reassignment(id, line_num, col_num),
            other => panic!("Expected = or function call, got {:?}", other)
        }
    }


    fn parse_reassignment(&mut self, id: String, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        // ensure that the current symbol both exists and is mutable
        match self.current_symbol_table.borrow().get(&id) {
            Some(symbol) => {
                if !symbol.mutable {
                    panic!("Semantic error: The identifier {} is immutable and cannot be reassigned", id)
                }
            },
            None => panic!("Semantic error: The identifier {} could not be found!", id)
        }

        let lhs = self.parse_lhs(SyntaxTree::new(SyntaxNode::Identifier(id), line_num, col_num), line_num, col_num)?;

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


    fn parse_lhs(&mut self, root: SyntaxTree, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::Equal => Ok(root),
            TokenType::OpenSquare => {
                let expr = self.parse_expression()?;

                let next_token = self.tokens.pop_front().unwrap();
                assert_token_type!(next_token, CloseSquare);

                self.parse_lhs(SyntaxTree::new(SyntaxNode::ArrayIndexingOperation(
                    Box::new(expr),
                    Box::new(root)
                ), line_num, col_num), line_num, col_num)
            }

            TokenType::Dot => {
                let next_token = self.tokens.pop_front().unwrap();
                let id = match next_token.token_type {
                    TokenType::Identifier(id) => SyntaxTree::new(
                        SyntaxNode::Identifier(id), 
                        next_token.line_number, 
                        next_token.col_number
                    ),
                    _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
                };

                self.parse_lhs(SyntaxTree::new(SyntaxNode::BinaryOperation(
                    ".".to_owned(), 
                    Box::new(root),
                    Box::new(id)
                ), line_num, col_num), line_num, col_num)
            }

            other => panic!("Invalid left expression, found {:?}", other)
        }
    }


    /// Parses a let statement
    /// 
    /// Let statements have the form: `"let" <identifier> ":" <type> "=" <expression> ";"`.
    fn parse_let_statement(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        let is_mutable = match self.tokens.front().unwrap().token_type {
            TokenType::MutKeyword => {
                self.tokens.pop_front();
                true
            }

            TokenType::ConstKeyword => {
                self.tokens.pop_front();
                false
            }

            _ => false
        };
        
        let next_token = self.tokens.pop_front().unwrap();
        let id: String = match next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
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
            SimpleType::Enum(_, _, None, _, _) => panic!("A raw enum is a type, not a value!"),
            _ => ()
        }

        if !expr_type.is_compatible_with(&var_type) {
            panic!(
                "Mismatch between variable type \n{:?} \nand expression type \n{:?} \non line {}, col {}!", 
                var_type.basic_type, 
                expr_type.basic_type,
                expression.start_line, 
                expression.start_index
            );
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Semicolon);

        let dependencies = calculate_computational_dependencies(&expression, &self.current_symbol_table.borrow()).unwrap();
        self.current_symbol_table.borrow_mut().insert(Symbol::new(SymbolType::Variable(id.clone(), var_type.clone(), dependencies), is_mutable, line_num, col_num));
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
    fn parse_type(&mut self) -> Result<Type, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        let basic_type = match next_token.token_type {
            TokenType::Identifier(id) => id,
            TokenType::OpenParen => return self.parse_tuple_type(),
            _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
        };

        // check if there is a generic component
        match self.tokens.get(0).unwrap().token_type {
            TokenType::LeftArrow => {
                self.tokens.pop_front().unwrap();

                let t = self.parse_type()?;
                
                let next_token = self.tokens.pop_front().unwrap();
                assert_token_type!(next_token, RightArrow);

                match basic_type.as_str() {
                    "IO" => return match &t.basic_type {
                        SimpleType::Void => Ok(Type::from_basic(SimpleType::IOMonad(Box::new(t), None))),
                        _ => Ok(Type::from_basic(SimpleType::IOMonad(Box::new(t.clone()), Some(Box::new(t)))))
                    },
                    _ => panic!()
                }
            }

            _ => () // no generic
        };

        let mut final_type: Type = Type::new_str(basic_type, false, vec![], &self.current_symbol_table.borrow()).unwrap();

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
                        return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseSquare));
                    }
                },
                _ => break
            }
        }

        Ok(final_type)
    }


    /// Parses a tuple type, which is a parenthesized list of types separated by commas
    fn parse_tuple_type(&mut self) -> Result<Type, ParsingError> {
        let mut types: Vec<Type> = vec![];
        loop {
            types.push(self.parse_type()?);

            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseParen => break,
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen))
            }
        }

        if types.len() < 2 {
            panic!("Tuple must have at least 2 elements!");
        }

        Ok(Type::new(SimpleType::Tuple(types), false, vec![]))
    }


    fn parse_while_loop(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
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


    fn parse_func_call_stmt(&mut self, id: String, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        // check that the function exists in this context
        match self.current_symbol_table.borrow().get(&id).unwrap().category {
            SymbolType::Function(_, _) => (),
            _ => panic!("Identifier {} is not a valid function name in this context", id)
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenParen);
        let call = self.parse_function_call(id, line_num, col_num);

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Semicolon);

        call
    }


    /// Parses a return statement after the return keyword has been popped from the queue of tokens
    /// 
    /// Validates that the return type is correct for the function it is returning from.
    fn parse_return(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        let expr: SyntaxTree = self.parse_expression()?;
        let expr_type: Type = get_expr_type(&expr, &self.current_symbol_table.borrow()).unwrap();
        // check that the returned value is type-compatible with the return type of the function
        match &self.current_return_type {
            Some(t) => if !self.in_monad && !expr_type.is_compatible_with(&t) {
                return Err(ParsingError::ReturnTypeMismatch(expr_type, t.clone(), line_num, col_num))
            }

            None => panic!()
        }

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
    pub fn parse_expression(&mut self) -> Result<SyntaxTree, ParsingError> {
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


    fn parse_logical_or(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_logical_and, DoublePipe => "||")
    }


    fn parse_logical_and(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_bitwise_xor, DoubleAmpersand => "&&")
    }
    
    
    fn parse_bitwise_xor(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_bitwise_or, UpArrow => "^")
    }


    fn parse_bitwise_or(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_bitwise_and, Pipe => "|")
    }


    fn parse_bitwise_and(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_equality, Ampersand => "&")
    }


    fn parse_equality(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_concatenation, DoubleEqual => "==", BangEqual => "!=")
    }
    
    
    // Could either be a concatenation or an enum instantiation
    fn parse_concatenation(&mut self) -> Result<SyntaxTree, ParsingError> {
        let mut root: SyntaxTree = self.parse_scalar_comparisons()?;
        let (root_line, root_col) = (root.start_line, root.start_index);
        
        // if the root is an identifier, check if it is for an enum, in which case it must be an
        // enum instantiation and not a raw type name
        let root_type = match root.node.clone() {
            SyntaxNode::Identifier(id) => {
                let rt = get_expr_type(&root, &self.current_symbol_table.borrow()).unwrap();
                match rt.basic_type {
                    SimpleType::Enum(name, _, None, _, _) => {
                        match self.current_symbol_table.clone().borrow().get(&id).unwrap().category {
                            // is an enum name and must be am instantiation
                            SymbolType::EnumeraionType(_, _, _) => return self.parse_enum_instantiation(root, name),
                            // is not an enum name
                            _ => get_expr_type(&root, &self.current_symbol_table.borrow()).unwrap()
                        }
                    },
                    _ => rt
                }
            }

            _ => get_expr_type(&root, &self.current_symbol_table.borrow()).unwrap()
        };
        
        match root_type.basic_type.clone() {
            SimpleType::Enum(_, _, _, _, _) => Ok(root),
            _ => { // is an array concatenation
                loop {
                    let next_token = match self.tokens.pop_front() {
                        Some(token) => token,
                        None => return Err(ParsingError::EarlyReturn(self.parse_right_assoc_unary()?))
                    };
                    
                    match next_token.token_type {
                        TokenType::DoubleColon => {
                            let right: SyntaxTree = self.parse_scalar_comparisons()?;
                            if let SimpleType::Str = root_type.basic_type {
                                root = SyntaxTree::new(
                                    SyntaxNode::ConcatStr(Box::new(root), Box::new(right),
                                ), root_line, root_col)
                            } else {
                                root = SyntaxTree::new(SyntaxNode::BinaryOperation(
                                    "::".to_owned(),
                                    Box::new(root),
                                    Box::new(right),
                                ), root_line, root_col);
                            }

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


    fn parse_enum_instantiation(&mut self, root: SyntaxTree, name: String) -> Result<SyntaxTree, ParsingError> {
        let (root_line, root_col) = (root.start_line, root.start_index);
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, DoubleColon);

        let next_token = self.tokens.pop_front().unwrap();
        let variant_id = match next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
        };

        let variant_params: IndexMap<String, SyntaxTree> = self.parse_enum_variant_params()?;
        let name_category = self.current_symbol_table.borrow().get(&name).unwrap().category;
        let enum_type = match &name_category {
            SymbolType::EnumeraionType(_, t, _) => t,
            _ => panic!()
        };

        match &enum_type.basic_type {
            SimpleType::Enum(_, variants, _, _, _) => {
                // check that the number of parameters passed to the variant matches the number of
                // parameters the variant has
                let enum_variant_params = variants.get(&variant_id).unwrap();
                assert_eq!(enum_variant_params.len(), variant_params.len());

                // check that the passed arguments have the correct type
                for (p_name, p_type) in enum_variant_params {
                    let variant_param_type = get_expr_type(
                        variant_params.get(p_name).unwrap(), 
                        &self.current_symbol_table.borrow()
                    ).unwrap();
                    
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


    fn parse_enum_variant_params(&mut self) -> Result<IndexMap<String, SyntaxTree>, ParsingError> {
        let mut variant_params: IndexMap<String, SyntaxTree> = IndexMap::new();
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::OpenParen => {
                loop {
                    // get the id of the argument
                    let next_token = self.tokens.pop_front().unwrap();
                    let arg_id = match next_token.token_type {
                        TokenType::Identifier(id) => id,
                        _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
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
                        _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen))
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


    fn parse_scalar_comparisons(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_shifts, RightArrow => ">", LeftArrow => "<", LeftArrowEqual => "<=", RightArrowEqual => ">=")
    }


    fn parse_shifts(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_plus_minus, DoubleRightArrow => ">>", TripleRightArrow => ">>>", DoubleLeftArrow => "<<")
    }


    fn parse_plus_minus(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_mult_div_modulo, Plus => "+", Minus => "-")
    }


    fn parse_mult_div_modulo(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_arrow, Star => "*", FwdSlash => "/", Percent => "%")
    }


    fn parse_arrow(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_right_assoc_unary, Arrow => "->")
    }


    fn parse_right_assoc_unary(&mut self) -> Result<SyntaxTree, ParsingError> {
        let next_token = match self.tokens.pop_front() {
            Some(token) => token,
            None => return Err(ParsingError::EarlyReturn(self.parse_right_assoc_unary()?))
        };

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

    fn parse_left_assoc_unary(&mut self) -> Result<SyntaxTree, ParsingError> {
        let mut root: SyntaxTree = self.parse_range()?;
        loop {
            let next_token = match self.tokens.pop_front() {
                Some(token) => token,
                None => return Err(ParsingError::EarlyReturn(root))
            };
            
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

                    if let TokenType::Dot = self.tokens.front().unwrap().token_type {
                        root = self.parse_dot_rhs(root)?
                    }
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


    fn parse_range(&mut self) -> Result<SyntaxTree, ParsingError> {
        parse_binary_operator!(self, parse_dot, DoubleDot => "..")
    }


    fn parse_dot(&mut self) -> Result<SyntaxTree, ParsingError> {
        let root: SyntaxTree = self.parse_cast()?;
        loop {
            let next_token = match self.tokens.front() {
                Some(token) => token,
                None => return Err(ParsingError::EarlyReturn(root))
            };

            match next_token.token_type {
                TokenType::Dot => {
                    self.tokens.pop_front().unwrap();
                    return self.parse_dot_rhs(root)
                },
                // End of this level of precedence
                _ => break
            }
        }

        Ok(root)
    }


    fn parse_dot_rhs(&mut self, left: SyntaxTree) -> Result<SyntaxTree, ParsingError> {
        let root = left;

        let root_type = get_expr_type(&root, &self.current_symbol_table.borrow()).unwrap(); 
        let (root_line, root_col) = (root.start_line, root.start_index);
        let mut root = match root_type.basic_type {
            // structs and enums support the . operator
            SimpleType::Struct(_, _, _) | SimpleType::Enum(_, _, _, _, _) => {
                let next_token = self.tokens.pop_front().unwrap();
                let following_token = self.tokens.front().unwrap();
                match next_token.token_type {
                    // we must have an identifier after the . operator
                    TokenType::Identifier(id) => {
                        match following_token.token_type {
                            // is a function call
                            TokenType::OpenParen => {
                                self.tokens.pop_front().unwrap();

                                let func_call_node = self.parse_function_call(id, next_token.line_number, next_token.col_number)?;
                                SyntaxTree::new(
                                    SyntaxNode::BinaryOperation(".".to_string(), Box::new(root), Box::new(func_call_node)), 
                                    root_line, root_col
                                )
                            }

                            // is a plain identifier
                            _ => {
                                let identifier_node = SyntaxTree::new(SyntaxNode::Identifier(id), root_line, root_col);
                                SyntaxTree::new(
                                    SyntaxNode::BinaryOperation(".".to_string(), Box::new(root), Box::new(identifier_node)), 
                                    root_line, root_col
                                )
                            }
                        }
                    }
                    _ => panic!()
                }
            }

            // the root is not an expression which supports the . operator
            _ => panic!()
        };

        if let TokenType::Dot = self.tokens.front().unwrap().token_type {
            self.tokens.pop_front().unwrap();
            root = self.parse_dot_rhs(root)?;
        }

        Ok(root)
    }


    fn parse_cast(&mut self) -> Result<SyntaxTree, ParsingError> {
        let mut root: SyntaxTree = self.parse_factor()?;
        let (root_line, root_col) = (root.start_line, root.start_index);

        let next_token = match self.tokens.pop_front() {
            Some(token) => token,
            None => return Err(ParsingError::EarlyReturn(root))
        };

        match next_token.token_type {
            TokenType::AsKeyword => {
                let right: Type = self.parse_type()?;
                let root_type: Type = get_expr_type(&root, &self.current_symbol_table.borrow()).unwrap();
                root = SyntaxTree::new(SyntaxNode::TypeCast(
                    right, root_type, Box::new(root)
                ), root_line, root_col);
            }

            // End of this level of precedence
            _ => self.tokens.push_front(next_token)
        }

        Ok(root)
    }


    /// Parses a factor, which is a literal, struct, function invocation, or parenthesized 
    /// expression.
    fn parse_factor(&mut self) -> Result<SyntaxTree, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::StrLiteral(s) => Ok(SyntaxTree::new(SyntaxNode::StringLiteral(s), next_token.line_number, next_token.col_number)),
            TokenType::IntLiteral(n) => Ok(SyntaxTree::new(SyntaxNode::IntLiteral(n), next_token.line_number, next_token.col_number)),
            TokenType::FloatLiteral(f) => Ok(SyntaxTree::new(SyntaxNode::FloatLiteral(f), next_token.line_number, next_token.col_number)),
            TokenType::BoolLiteral(b) => Ok(SyntaxTree::new(SyntaxNode::BoolLiteral(b), next_token.line_number, next_token.col_number)),
            TokenType::SelfKeyword => Ok(SyntaxTree::new(SyntaxNode::SelfIdentifier, next_token.line_number, next_token.col_number)),
            TokenType::DoKeyword => self.parse_do_block(),
            TokenType::Identifier(id) => self.parse_identifier_factor(id, next_token.line_number, next_token.col_number),
            TokenType::OpenParen => self.parse_tuple_or_paren_expr(),
            TokenType::OpenSquare => self.parse_array_literal(next_token.line_number, next_token.col_number),
            _ => Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Expression))
        }
    }


    /// If there is an identifier in a factor which has already been parsed, check if it is a 
    /// regular identifier or if it is part of a function call or struct instantiation, in which 
    /// case parse those.
    fn parse_identifier_factor(&mut self, id: String, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        // check that the identifier is valid in this context
        match self.current_symbol_table.borrow().get(&id) {
            Some(_) => (),
            None => panic!("Semantic error: The identifier {} could not be found on line {}, col {}!", id, line_num, col_num)
        }

        // peek at the next token, but don't pop it yet
        let peek_next_token = match self.tokens.pop_front() {
            Some(token) => token,
            None => return Err(ParsingError::EarlyReturn(SyntaxTree::new(SyntaxNode::Identifier(id), line_num, col_num)))
        };

        match peek_next_token.token_type {
            // function call
            TokenType::OpenParen => self.parse_function_call(id, peek_next_token.line_number, peek_next_token.col_number),
            TokenType::OpenCurly => { // struct instantiation
                let members = self.parse_struct_instantiation_members(&id)?;
                return Ok(SyntaxTree::new(SyntaxNode::StructInstantiation(id, members), line_num, col_num))
            } 

            _ => { // regular identifier
                self.tokens.push_front(peek_next_token);
                return Ok(SyntaxTree::new(SyntaxNode::Identifier(id), line_num, col_num));
            }
        }
    }


    /// Parses a function call and its arguments, will return an error if a monad is returned from 
    /// outside a monadic context
    fn parse_function_call(&mut self, id: String, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        let arguments: Vec<SyntaxTree> = self.parse_func_args()?;
        let return_type = self.current_symbol_table.borrow().get(&id).unwrap();

        match return_type.get_type().basic_type {
            SimpleType::IOMonad(_, _) => {
                if !self.in_monad {
                    panic!("Use of monad outside monadic context!");
                }

                Ok(SyntaxTree::new(SyntaxNode::FunctionCall(id, arguments), line_num, col_num))
            },
            _ => Ok(SyntaxTree::new(SyntaxNode::FunctionCall(id, arguments), line_num, col_num))
        } 
    }

    /// Parses a struct instantiation where the identifier has already been parsed. This follows 
    /// this grammar:
    /// 
    /// STRUCT_INSTANTIATION ::= "struct" <IDENTIFIER> "{" <STRUCT_MEMBER> "}"
    /// STRUCT_MEMBER ::= <IDENTIFIER> : <EXPRESSION> "," <STRUCT_MEMBER> | <IDENTIFIER> : <EXPRESSION>
    fn parse_struct_instantiation_members(&mut self, struct_id: &str) -> Result<IndexMap<String, SyntaxTree>, ParsingError> {
        // get all the comma-separated members of the struct
        let mut members: IndexMap<String, SyntaxTree> = IndexMap::new();
        loop {
            let next_token = self.tokens.pop_front().unwrap();
            let id = match next_token.token_type {
                TokenType::Identifier(id) => id,
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
            };

            let next_token = self.tokens.pop_front().unwrap();
            assert_token_type!(next_token, Colon);

            let expr = self.parse_expression()?;
            members.insert(id, expr);

            // if the next token is a comma, continue, if it is a curly bracket, this is the end 
            // of the declaration
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseCurly => break,
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseCurly))
            }
        }

        // ensure that the members of the instantiation are stored in the same order they are 
        // declared in the struct declaration 
        let mut ordered_members: IndexMap<String, SyntaxTree> = IndexMap::new();
        let struct_type: Type = self.current_symbol_table.borrow().get(&struct_id.to_owned()).unwrap().get_type();
        match struct_type.basic_type {
            SimpleType::Struct(_, m, _) => {
                for key in m.keys() {
                    // TODO: make this more efficient by removing the clones
                    ordered_members.insert(key.clone(), members.get(key).unwrap().clone());
                }
            }
            _ => panic!()
        }

        Ok(ordered_members)
    }


    fn parse_array_literal(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        let mut elems: Vec<SyntaxTree> = vec![];
        loop {
            elems.push(self.parse_expression()?);
            let next_token = self.tokens.pop_front().unwrap();
            match &next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseSquare => break,
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseSquare))
            } 
        }

        let inner_type = get_expr_type(elems.get(0).unwrap(), &self.current_symbol_table.borrow()).unwrap();
        Ok(SyntaxTree::new(SyntaxNode::ArrayLiteral(elems, inner_type), line_num, col_num))
    } 


    /// Used when it is unclear if the next set of tokens represents a parenthesized expression or
    /// a tuple. This can be determined by seeing if the first expression encountered ends with a
    /// comma, making it a tuple, or a close parenthesis, making it a parenthesized expression.
    fn parse_tuple_or_paren_expr(&mut self) -> Result<SyntaxTree, ParsingError> {
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
    fn parse_tuple(&mut self, first_expr: SyntaxTree, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
        let mut expressions: Vec<SyntaxTree> = vec![first_expr];
        loop {
            expressions.push(self.parse_expression()?);
            let next_token = self.tokens.pop_front().unwrap();
            match &next_token.token_type {
                TokenType::Comma => continue,
                TokenType::CloseParen => break,
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen))
            } 
        }

        Ok(SyntaxTree::new(SyntaxNode::TupleLiteral(expressions), line_num, col_num))
    }


    fn parse_identifier(&mut self) -> Result<String, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        if let TokenType::Identifier(id) = next_token.token_type {
            return Ok(id)
        }

        Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
    }


    /// Produces a monadic action such as `IO<()>` or `IO<str>`.
    /// 
    /// The value contained within a monad cannot be extracted from a monad outside of another
    /// monad, as in Haskell, for example. This ensures that side effects, such as reading and
    /// writing from standard I/O, are properly ordered and are not parallelized, causing problems
    /// with out-of-order effects - this is why monads are never parallelized.
    fn parse_do_block(&mut self) -> Result<SyntaxTree, ParsingError> {
        self.in_monad = true;

        let param: Option<(String, Type)> = self.parse_do_block_param()?;
        let next_token = self.tokens.pop_front().unwrap();
        let (line, col) = (next_token.line_number, next_token.col_number);
        assert_token_type!(next_token, OpenCurly);

        // parse the body of the monad, adding a symbol for the monad's parameter if there is one
        let body = match &param {
            Some(p) => self.parse_stmt_block(vec![Symbol::new(SymbolType::Variable(p.0.clone(), p.1.clone(), vec![]), false, 0, 0)])?,
            None => self.parse_stmt_block(vec![])?
        };

        // get the return type of the monad, which defaults to IO<void>, if the return type is a
        // monad, flatten the Monad<Monad<T>> to Monad<T>
        let default = Type::from_basic(SimpleType::IOMonad(Box::new(Type::from_basic(SimpleType::Void)), None));
        let return_type = get_monad_return_type(&body, &self.current_symbol_table.borrow()).unwrap_or(default);
        let return_type = match &return_type.basic_type {
            SimpleType::IOMonad(rt, _) => *rt.to_owned(),
            _ => return_type
        };

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseCurly);

        self.in_monad = false;
        Ok(SyntaxTree::new(SyntaxNode::MonadicExpr(Box::new(body), param, return_type), line, col))
    }


    fn parse_do_block_param(&mut self) -> Result<Option<(String, Type)>, ParsingError> {
        match self.tokens.front().unwrap().token_type {
            TokenType::OpenParen => {
                self.tokens.pop_front().unwrap();
                let identifier = match self.tokens.get(0).unwrap().token_type {
                    TokenType::CloseParen => {
                        self.tokens.pop_front().unwrap();
                        return Ok(None)
                    },
                    TokenType::Identifier(_) => Some(self.parse_identifier()?),
                    _ => panic!()
                };

                let next_token = self.tokens.pop_front().unwrap();
                assert_token_type!(next_token, Colon);

                let t = self.parse_type()?;

                let next_token = self.tokens.pop_front().unwrap();
                assert_token_type!(next_token, CloseParen);

                Ok(Some((identifier.unwrap(), t)))
            }
            _ => Ok(None)
        }
    }


    fn parse_func_args(&mut self) -> Result<Vec<SyntaxTree>, ParsingError> {
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
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen))
            }
        }

        Ok(args)
    }


    fn parse_selection(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, ParsingError> {
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


    fn parse_enumeration(&mut self, start_line: usize, start_index: usize) -> Result<SyntaxTree, ParsingError> {
        self.current_return_type = None;

        let next_token = self.tokens.pop_front().unwrap();
        let identifier = match next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
        };

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenCurly);

        let variants = self.parse_enum_variants()?;
        let variant_data = self.get_enum_variants_data(&variants);

        // create a new frame in the symbol table and set the current symbol tableto the new one
        let old_symbol_table = self.current_symbol_table.clone();
        self.current_symbol_table = SymbolTable::add_child(&self.current_symbol_table);

        // create a new symbol for the new struct, call it self as that is how it will be referred
        // to in the definition context, and add it to the symbol table
        let self_symbol = Symbol::new(SymbolType::StructType(
            "self".to_owned(),
            Type::from_basic(SimpleType::Enum(identifier.clone(), variant_data.clone(), None, HashMap::new(), vec![])) 
        ), false, 0, 0);
        self.current_symbol_table.borrow_mut().insert(self_symbol);

        let next_token = self.tokens.front().unwrap();
        let methods: HashMap<String, SyntaxTree> = match next_token.token_type {
            TokenType::WithKeyword => {
                self.tokens.pop_front();
                self.parse_methods()?
            }
            _ => HashMap::new()
        };

        // restore the old symbol table now that we are done with the struct definition context
        self.current_symbol_table = old_symbol_table.clone();
        
        let method_types: HashMap<String, Box<Type>> = methods.iter()
                                                              .map(|(k, v)| (k.clone(), Box::new(get_function_type(v))))
                                                              .collect();

        let t: Type = Type::from_basic(SimpleType::Enum(identifier.clone(), variant_data, None, method_types, vec![]));
        self.current_symbol_table.borrow_mut().insert(
            Symbol::new(SymbolType::EnumeraionType(identifier.clone(), t.clone(), vec![]), 
            false, start_line, start_index)
        );
        Ok(SyntaxTree::new(SyntaxNode::Enumeraion(identifier, variants, methods), start_line, start_index))
    }


    fn parse_enum_variants(&mut self) -> Result<Vec<SyntaxTree>, ParsingError> {
        let mut variants: Vec<SyntaxTree> = vec![];
        variants.push(self.parse_enum_variant()?);

        loop {
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Comma => variants.push(self.parse_enum_variant()?),
                TokenType::CloseCurly => break,
                _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Semicolon))
            }
        }

        Ok(variants)
    }


    fn parse_enum_variant(&mut self) -> Result<SyntaxTree, ParsingError> {
        // get the enum variant name
        let next_token = self.tokens.pop_front().unwrap();
        let identifier = match next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
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
                        _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier))
                    }

                    // end the loop if it is the end of the params list, or continue if there is
                    // another parameter
                    let next_token = self.tokens.pop_front().unwrap();
                    match next_token.token_type {
                        TokenType::CloseParen => break,
                        TokenType::Comma => continue,
                        _ => return Err(ParsingError::UnexpectedToken(next_token, ExpectedToken::CloseParen))
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


#[cfg(test)]
mod tests {
    use crate::Scanner;

    use super::Parser;
    
    
    #[test]
    fn test_mutable_variable_reassignment() {
        let scanner = Scanner::from_str("
            fn main() -> i32 {
                let mut a: i32 = 1;
                a = 2;
                return a;
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_immutable_variable_reassignment() {
        let scanner = Scanner::from_str("
            fn main() -> i32 {
                let a: i32 = 1;
                a = 2;
                return a;
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_incorrect_return_type() {
        let scanner = Scanner::new("tests/test_incorrect_return_type.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_io_outside_monad() {
        let scanner = Scanner::new("tests/test_io_outside_monad.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_io_outside_monad_expr() {
        let scanner = Scanner::new("tests/test_io_outside_monad_expr.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }
}
