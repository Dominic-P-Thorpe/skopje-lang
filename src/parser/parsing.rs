use std::collections::{HashMap, VecDeque};
use std::error::Error;

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
pub enum SyntaxNode {
    Program(Vec<SyntaxTree>),
    // function name, arguments (id, type), return type, body statements
    Function(String, Vec<(String, Type)>, Type, Vec<SyntaxTree>),
    // expression to return
    ReturnStmt(Box<SyntaxTree>),
    // condition, body
    WhileStmt(Box<SyntaxTree>, Vec<SyntaxTree>),
    // Loop variable name, loop var type, expr to loop over, loop body
    ForStmt(String, Type, Box<SyntaxTree>, Vec<SyntaxTree>),
    // variable name, type, expression
    LetStmt(String, Type, Box<SyntaxTree>),
    // variable name, new value expression, type of the variable being reassigned
    // type is needed so that is can be used when generating the C++ code
    ReassignmentStmt(Box<SyntaxTree>, Box<SyntaxTree>, Type),
    // condition, body, optional else
    SelectionStatement(Box<SyntaxTree>, Vec<SyntaxTree>, Option<Vec<SyntaxTree>>),
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
    MonadicExpr(Vec<SyntaxTree>),
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
    Identifier(String) 
}


#[derive(Debug, Clone, PartialEq)]
pub struct SyntaxTree {
    pub node: SyntaxNode,
    start_index: usize,
    start_line: usize
}


impl SyntaxTree {
    pub fn new(node: SyntaxNode, start_line: usize, start_index: usize) -> Self {
        SyntaxTree {
            node, start_index, start_line
        }
    }
}


/// Represents the current semantic context of the compiler, necessary for debugging and semantic
/// checking.
/// 
/// Contains information about the identifiers which are valid for use in the current context, such
/// as their type.
pub struct Context {
    /// The valid identifiers in this context and their types
    pub valid_identifiers: HashMap<String, (Type, usize)>,
    context_window_id: usize
}


impl Context {
    pub fn new() -> Self {
        let mut valid_identifiers: HashMap<String, (Type, usize)> = HashMap::new();
        valid_identifiers.insert("print".to_owned(), (Type::new(SimpleType::Function (
            Box::new(Type::from_basic(SimpleType::IOMonad)), vec![
                Type::from_basic(SimpleType::Str)
            ]), 
            false, vec![]), 0)
        );
        valid_identifiers.insert("readln".to_owned(), (Type::new(SimpleType::Function (
            Box::new(Type::from_basic(SimpleType::IOMonad)), vec![
                Type::from_basic(SimpleType::Str)
            ]), 
            false, vec![]), 0)
        );

        Context {
            valid_identifiers,
            context_window_id: 1
        }
    }


    pub fn add_var(&mut self, id: String, t: Type) {
        self.valid_identifiers.insert(id, (t, self.context_window_id));
    }


    pub fn start_new_context_window(&mut self) -> usize {
        self.context_window_id += 1;
        self.context_window_id
    }


    pub fn end_context_window(&mut self, context_window: &usize) {
        self.valid_identifiers = self.valid_identifiers
                                     .iter()
                                     .filter(|(_, (_, window_id))| window_id != context_window)
                                     .map(|(k, (t, w))| (k.clone(), (t.clone(), *w)))
                                     .collect();
    }


    /// Checks if the passed identifier is a valid function in the given context and returns the
    /// type of the function if it is, and `None` if it isn't.
    pub fn verify_function(&self, func_name: &String) -> Option<Type> {
        match self.valid_identifiers.get(func_name) {
            Some((func_type, _)) => {
                match func_type.basic_type {
                    SimpleType::Function(_, _) => Some(func_type.clone()),
                    _ => None
                }
            }

            None => None
        }
    }
}


/// Contains a [`VecDeque`] of tokens which can be used as a FIFO queue data structure. 
/// 
/// This data structure is modified by the parser as tokens are sequentially popped off of the front
/// of the queue and organized into the AST.
pub struct Parser {
    tokens: VecDeque<Token>,
    context: Context
}


impl Parser {
    /// Creates a [`VecDeque`] of tokens which can be used as a FIFO queue data structure in the
    /// [`Parser`] struct.  
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser { 
            tokens: VecDeque::from(tokens),
            context: Context::new()
        }
    }


    pub fn parse(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        let mut top_level_constructs: Vec<SyntaxTree> = vec![];
        while let Some(next_token) = self.tokens.pop_front() {
            match &next_token.token_type {
                TokenType::FnKeyword => top_level_constructs.push(self.parse_function(next_token.line_number, next_token.col_number)?),
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::FnKeyword)))
            }
        }

        Ok(SyntaxTree::new(SyntaxNode::Program(top_level_constructs), 0, 0))
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
        let context_window_id: usize = self.context.start_new_context_window();

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
            
            let body = self.parse_stmt_block()?;
            
            let close_body = self.tokens.pop_front().unwrap();
            assert_token_type!(close_body, CloseCurly);
            
            // add this function to the valid functions available in this context
            let func_type = Type::new(SimpleType::Function(
                Box::new(return_type.clone()), params.iter().map(|(_, t)| t).cloned().collect::<Vec<Type>>()
            ), false, vec![]);
            self.context.add_var(id.clone(), func_type);

            self.context.end_context_window(&context_window_id);
            return Ok(SyntaxTree::new(
                SyntaxNode::Function(id, params, return_type, body), line_num, col_num
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
            let p_id: String;

            let next_token = self.tokens.pop_front().unwrap();
            if let TokenType::Identifier(id) = next_token.token_type {
                p_id = id;
            } else {
                return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Identifier)));
            }

            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Colon => (),
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Colon)))
            }

            // TODO: make this work with all param types
            let p_type: Type = self.parse_type().unwrap();

            params.push((p_id.clone(), p_type.clone()));
            self.context.add_var(p_id, p_type);

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
    fn parse_stmt_block(&mut self) -> Result<Vec<SyntaxTree>, Box<dyn Error>> {
        let context_window_id: usize = self.context.start_new_context_window();
        let mut statements: Vec<SyntaxTree> = vec![];
        loop {
            let statement = self.parse_statement()?;
            statements.push(statement);

            if let TokenType::CloseCurly = self.tokens.get(0).unwrap().token_type {
                break;
            }
        }

        self.context.end_context_window(&context_window_id);
        Ok(statements)
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
            _ => Err(Box::new(ParsingError::UnexpectedToken(next_token, ExpectedToken::Statement)))
        }
    }


    /// Parses a for loop which should conform to the EBNF:
    /// 
    /// `FOR_LOOP ::= "for" "(" <IDENTIFIER> ":" <TYPE> "in" <EXPRESSION> ")" "{" <BODY> "}"`
    fn parse_for_loop(&mut self, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenParen);

        let next_token = self.tokens.pop_front().unwrap();
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
        let iterator_expr_type = get_expr_type(&iterator_expr, &self.context).unwrap();
        println!("Type: {:?}", iterator_expr_type);
        if !iterator_type.is_compatible_with(&get_array_inner_type(&iterator_expr_type)) {
            panic!("Iterator variable type must be compatible with the type of the elements of the iterator expression!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseParen);
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenCurly);

        self.context.add_var(iterator_id.clone(), iterator_type.clone());
        let body = self.parse_stmt_block()?;

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseCurly);

        Ok(SyntaxTree::new(SyntaxNode::ForStmt(iterator_id, iterator_type, Box::new(iterator_expr), body), line_num, col_num))
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
        match self.context.valid_identifiers.get(&id) {
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
        let expr_type: Type = get_expr_type(&expr, &self.context).unwrap();
        let lhs_type: Type = get_l_expr_type(&lhs, &self.context).unwrap();
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
        let expr_type: Type = get_expr_type(&expression, &self.context).unwrap();
        if !var_type.is_compatible_with(&expr_type) {
            panic!("Mismatch between variable and expression types!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Semicolon);

        self.context.add_var(id.clone(), var_type.clone());
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

        let mut final_type: Type = Type::new_str(basic_type, false, generics)?;

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
        if get_expr_type(&expr, &self.context).unwrap() != Type::new(SimpleType::Bool, false, vec![]) {
            panic!("If statement's condition must be of type bool!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseParen);
        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenCurly);

        let body = self.parse_stmt_block()?;

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseCurly);

        Ok(SyntaxTree::new(SyntaxNode::WhileStmt(Box::new(expr), body), line_num, col_num))
    }


    fn parse_func_call_stmt(&mut self, id: String, line_num: usize, col_num: usize) -> Result<SyntaxTree, Box<dyn Error>> {
        // check that the function exists in this context
        match self.context.verify_function(&id) {
            Some(_) => (),
            None => panic!("Identifier {} is not valid in this context", id)
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, OpenParen);

        let arguments: Vec<SyntaxTree> = self.parse_func_args()?;

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, Semicolon);
        
        let expr = SyntaxTree::new(SyntaxNode::FunctionCallStmt(id, arguments), line_num, col_num);
        get_expr_type(&expr, &self.context).unwrap();
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
    
    
    fn parse_concatenation(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        parse_binary_operator!(self, parse_scalar_comparisons, DoubleColon => "::")
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
                    let root_type: Type = get_expr_type(&root, &self.context).unwrap();
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
                match self.context.valid_identifiers.get(&id) {
                    Some(_) => (),
                    None => panic!("Semantic error: The identifier {} could not be found!", id)
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

        let inner_type = get_expr_type(elems.get(0).unwrap(), &self.context)?;
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

        let body = self.parse_stmt_block()?;

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseCurly);

        Ok(SyntaxTree::new(SyntaxNode::MonadicExpr(body), line, col))
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
        if get_expr_type(&cond, &self.context).unwrap() != Type::new(SimpleType::Bool, false, vec![]) {
            panic!("If statement's condition must be of type bool!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert_token_type!(next_token, CloseParen);

        let next_token = self.tokens.pop_front().unwrap();
        let if_body = match next_token.token_type {
            TokenType::OpenCurly => {
                let result = self.parse_stmt_block()?;
                let next_token = self.tokens.pop_front().unwrap();
                assert_token_type!(next_token, CloseCurly);
                result
            },

            _ => {
                self.tokens.push_front(next_token);
                vec![self.parse_statement()?]
            }
        };

        let next_token = self.tokens.pop_front().unwrap();
        let else_body = match next_token.token_type {
            TokenType::ElseKeyword => {
                let next_token = self.tokens.pop_front().unwrap();
                Some(match next_token.token_type {
                    TokenType::OpenCurly => {
                        let result = self.parse_stmt_block()?;
                        let next_token = self.tokens.pop_front().unwrap();
                        assert_token_type!(next_token, CloseCurly);
                        result
                    },

                    _ => {
                        self.tokens.push_front(next_token);
                        vec![self.parse_statement()?]
                    }
                })
            },

            _ => {
                self.tokens.push_front(next_token);
                None
            }
        };

        Ok(SyntaxTree::new(SyntaxNode::SelectionStatement(Box::new(cond), if_body, else_body), line_num, col_num))
    }
}
