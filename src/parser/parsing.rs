use std::collections::{HashMap, VecDeque};
use std::error::Error;

use crate::semantics::typechecking::get_expr_type;

use super::types::SimpleType;
use super::{errors::ParsingError, token::*, types::Type};


macro_rules! parse_binary_operator {
    ($self:ident, $next:ident, $($op_type:ident => $op_str:expr),*) => {{
        let mut root: SyntaxTree = $self.$next()?;

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
                        ));
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


#[derive(Debug, Clone, PartialEq)]
pub enum SyntaxNode {
    Program(Vec<SyntaxTree>),
    // function name, arguments (id, type), return type, body statements
    Function(String, Vec<(String, Type)>, Type, Vec<SyntaxTree>),
    // expression to return
    ReturnStmt(Box<SyntaxTree>),
    // condition, body
    WhileStmt(Box<SyntaxTree>, Vec<SyntaxTree>),
    // variable name, type, expression
    LetStmt(String, Type, Box<SyntaxTree>),
    // variable name, new value expression
    ReassignmentStmt(String, Box<SyntaxTree>),
    // condition, body, optional else
    SelectionStatement(Box<SyntaxTree>, Vec<SyntaxTree>, Option<Vec<SyntaxTree>>),
    // binary operation, left side, right side
    BinaryOperation(String, Box<SyntaxTree>, Box<SyntaxTree>),
    RightAssocUnaryOperation(String, Box<SyntaxTree>),
    LeftAssocUnaryOperation(String, Box<SyntaxTree>),
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
    Identifier(String)
}


#[derive(Debug, Clone, PartialEq)]
pub struct SyntaxTree {
    pub node: SyntaxNode,
    start_index: u64,
    start_line: u64,
    end_index: u64,
    end_line: u64
}


impl SyntaxTree {
    pub fn new(node: SyntaxNode) -> Self {
        SyntaxTree {
            node, start_index: 0, start_line: 0, end_index: 0, end_line: 0
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
        valid_identifiers.insert("print".to_owned(), (Type::new(SimpleType::Void, false, vec![]), 0));
        valid_identifiers.insert("readln".to_owned(), (Type::new(SimpleType::Void, false, vec![]), 0));

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
                TokenType::FnKeyword => top_level_constructs.push(self.parse_function()?),
                _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token)))
            }
        }

        Ok(SyntaxTree::new(SyntaxNode::Program(top_level_constructs)))
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
    fn parse_function(&mut self) -> Result<SyntaxTree, Box<dyn Error>> {
        let id_token = self.tokens.pop_front().unwrap();
        if let TokenType::Identifier(id) = id_token.token_type {
            let open_paren = self.tokens.pop_front().unwrap();
            assert!(matches!(open_paren.token_type, TokenType::OpenParen));

            let params: Vec<(String, Type)> = self.parse_func_params()?;

            let arrow = self.tokens.pop_front().unwrap();
            assert!(matches!(arrow.token_type, TokenType::Arrow));

            let return_type = self.parse_type().unwrap();

            let open_body = self.tokens.pop_front().unwrap();
            assert!(matches!(open_body.token_type, TokenType::OpenCurly));
            
            let body = self.parse_stmt_block()?;
            
            let close_body = self.tokens.pop_front().unwrap();
            assert!(matches!(close_body.token_type, TokenType::CloseCurly));
            
            // add this function to the valid functions available in this context
            let func_type = Type::new(SimpleType::Function(
                Box::new(return_type.clone()), params.iter().map(|(_, t)| t).cloned().collect::<Vec<Type>>()
            ), false, vec![]);
            self.context.add_var(id.clone(), func_type);

            return Ok(SyntaxTree::new(
                SyntaxNode::Function(id, params, return_type, body)
            ));
        }

        Err(Box::new(ParsingError::UnexpectedToken(id_token)))
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
            let p_id: String; 
            let p_type: Type;

            let next_token = self.tokens.pop_front().unwrap();
            if let TokenType::Identifier(id) = next_token.token_type {
                p_id = id;
            } else {
                return Err(ParsingError::UnexpectedToken(next_token));
            }

            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::Colon => (),
                _ => return Err(ParsingError::UnexpectedToken(next_token))
            }

            // TODO: make this work with all param types
            let next_token = self.tokens.pop_front().unwrap();
            if let TokenType::Identifier(t) = next_token.token_type {
                p_type = Type::new_str(t, false, vec![]).unwrap();
            } else {
                return Err(ParsingError::UnexpectedToken(next_token));
            }

            params.push((p_id, p_type));

            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::CloseParen => break,
                TokenType::Comma => continue,
                _ => return Err(ParsingError::UnexpectedToken(next_token))
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
    fn parse_stmt_block(&mut self) -> Result<Vec<SyntaxTree>, ParsingError> {
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


    fn parse_statement(&mut self) -> Result<SyntaxTree, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::ReturnKeyword => self.parse_return(),
            TokenType::IfKeyword => self.parse_selection(),
            TokenType::WhileKeyword => self.parse_while_loop(),
            TokenType::Identifier(id) => self.parse_func_call_or_reassignment_stmt(id),
            TokenType::LetKeyword => self.parse_let_statement(),
            _ => Err(ParsingError::UnexpectedToken(next_token))
        }
    }


    fn parse_func_call_or_reassignment_stmt(&mut self, id: String) -> Result<SyntaxTree, ParsingError> {
        let next_token = self.tokens.get(0).unwrap();
        match next_token.token_type {
            TokenType::OpenParen => self.parse_func_call_stmt(id),
            TokenType::Equal => self.parse_reassignment(id),
            _ => Err(ParsingError::UnexpectedToken(next_token.clone()))
        }
    }


    fn parse_reassignment(&mut self, id: String) -> Result<SyntaxTree, ParsingError> {
        match self.context.valid_identifiers.get(&id) {
            Some(_) => (),
            None => panic!("Semantic error: The identifier {} could not be found!", id)
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::Equal));

        let expr = self.parse_expression()?;
        let expr_type: Type = get_expr_type(&expr, &self.context).unwrap();
        if expr_type != self.context.valid_identifiers.get(&id).unwrap().0 {
            panic!("Mismatch between variable and expression types!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::Semicolon));

        Ok(SyntaxTree::new(SyntaxNode::ReassignmentStmt(id, Box::new(expr))))
    }


    /// Parses a let statement
    /// 
    /// Let statements have the form: `"let" <identifier> ":" <type> "=" <expression> ";"`.
    fn parse_let_statement(&mut self) -> Result<SyntaxTree, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        let id: String = match next_token.token_type {
            TokenType::Identifier(id) => id,
            _ => return Err(ParsingError::UnexpectedToken(next_token))
        };

        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::Colon));

        let var_type = self.parse_type().unwrap();

        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::Equal));

        let expression: SyntaxTree = self.parse_expression()?;
        let expr_type: Type = get_expr_type(&expression, &self.context).unwrap();
        if !var_type.is_compatible_with(&expr_type) {
            panic!("Mismatch between variable and expression types!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::Semicolon));

        self.context.add_var(id.clone(), var_type.clone());
        Ok(SyntaxTree::new(SyntaxNode::LetStmt(id, var_type, Box::new(expression))))
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
            _ => return Err(Box::new(ParsingError::UnexpectedToken(next_token)))
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

        Ok(Type::new_str(basic_type, false, generics)?)
    }


    fn parse_while_loop(&mut self) -> Result<SyntaxTree, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::OpenParen));

        let expr = self.parse_expression()?;
        if get_expr_type(&expr, &self.context).unwrap() != Type::new(SimpleType::Bool, false, vec![]) {
            panic!("If statement's condition must be of type bool!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::CloseParen));
        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::OpenCurly));

        let body = self.parse_stmt_block()?;

        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::CloseCurly));

        Ok(SyntaxTree::new(SyntaxNode::WhileStmt(Box::new(expr), body)))
    }


    fn parse_func_call_stmt(&mut self, id: String) -> Result<SyntaxTree, ParsingError> {
        // check that the function exists in this context
        match self.context.verify_function(&id) {
            Some(_) => (),
            None => panic!("Identifier {} is not valid in this context", id)
        }

        let next_token = self.tokens.pop_front().unwrap();
        if let TokenType::OpenParen = next_token.token_type {
            let arguments: Vec<SyntaxTree> = self.parse_func_args()?;
            if let TokenType::Semicolon = self.tokens.pop_front().unwrap().token_type {
                let expr = SyntaxTree::new(SyntaxNode::FunctionCallStmt(id, arguments));
                get_expr_type(&expr, &self.context).unwrap();
                return Ok(expr);
            }
        }
        
        Err(ParsingError::UnexpectedToken(next_token))
    }


    fn parse_return(&mut self) -> Result<SyntaxTree, ParsingError> {
        let expr = self.parse_expression()?;
        if let TokenType::Semicolon = self.tokens.pop_front().unwrap().token_type {
            return Ok(SyntaxTree::new(SyntaxNode::ReturnStmt(Box::new(expr))));
        }

        Err(ParsingError::MissingSemicolon(0))
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
    fn parse_expression(&mut self) -> Result<SyntaxTree, ParsingError> {
        let left = self.parse_logical_or()?;
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::Question => {
                let true_expr: SyntaxTree = self.parse_expression()?;
                let next_token = self.tokens.pop_front().unwrap();
                if let TokenType::Colon = next_token.token_type {
                    let false_expr: SyntaxTree = self.parse_expression()?;
                    return Ok(SyntaxTree::new(SyntaxNode::TernaryExpression(
                        Box::new(left), Box::new(true_expr), Box::new(false_expr)
                    )));

                }

                return Err(ParsingError::UnexpectedToken(next_token));
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
        parse_binary_operator!(self, parse_scalar_comparisons, DoubleEqual => "==", BangEqual => "!=")
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
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::Minus => Ok(SyntaxTree::new(SyntaxNode::RightAssocUnaryOperation(
                "-".to_owned(),
                Box::new(self.parse_right_assoc_unary()?),
            ))),

            TokenType::Plus => Ok(SyntaxTree::new(SyntaxNode::RightAssocUnaryOperation(
                "+".to_owned(),
                Box::new(self.parse_right_assoc_unary()?),
            ))),

            TokenType::Bang => Ok(SyntaxTree::new(SyntaxNode::RightAssocUnaryOperation(
                "!".to_owned(),
                Box::new(self.parse_right_assoc_unary()?),
            ))),

            TokenType::Complement => Ok(SyntaxTree::new(SyntaxNode::RightAssocUnaryOperation(
                "~".to_owned(),
                Box::new(self.parse_right_assoc_unary()?),
            ))),

            // End of this level of precedence
            _ => {
                self.tokens.push_front(next_token);
                self.parse_left_assoc_unary()
            }
        }
    }

    fn parse_left_assoc_unary(&mut self) -> Result<SyntaxTree, ParsingError> {
        let mut root: SyntaxTree = self.parse_factor()?;
        loop {
            let next_token = self.tokens.pop_front().unwrap();
            match next_token.token_type {
                TokenType::DoublePlus => {
                    root = SyntaxTree::new(SyntaxNode::LeftAssocUnaryOperation(
                        "++".to_owned(),
                        Box::new(root),
                    ));
                }

                TokenType::DoubleMinus => {
                    root = SyntaxTree::new(SyntaxNode::LeftAssocUnaryOperation(
                        "--".to_owned(),
                        Box::new(root),
                    ));
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


    /// Parses a factor, which is a literal, function invocation, or parenthesized expression.
    fn parse_factor(&mut self) -> Result<SyntaxTree, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        match next_token.token_type {
            TokenType::StrLiteral(s) => Ok(SyntaxTree::new(SyntaxNode::StringLiteral(s))),
            TokenType::IntLiteral(n) => Ok(SyntaxTree::new(SyntaxNode::IntLiteral(n))),
            TokenType::BoolLiteral(b) => Ok(SyntaxTree::new(SyntaxNode::BoolLiteral(b))),
            TokenType::DoKeyword => self.parse_do_block(),

            TokenType::Identifier(id) => {
                // check that the identifier is valid in this context
                match self.context.valid_identifiers.get(&id) {
                    Some(_) => (),
                    None => panic!("Semantic error: The identifier {} could not be found!", id)
                }

                let next_token = self.tokens.pop_front().unwrap();
                match next_token.token_type {
                    TokenType::OpenParen => { // function call
                        let arguments: Vec<SyntaxTree> = self.parse_func_args()?;
                        return Ok(SyntaxTree::new(SyntaxNode::FunctionCall(id, arguments)));
                    }

                    _ => {
                        self.tokens.push_front(next_token);
                        return Ok(SyntaxTree::new(SyntaxNode::Identifier(id)));
                    }
                }
            }

            TokenType::OpenParen => {
                let expr: SyntaxTree = self.parse_expression()?;
                let next_token = self.tokens.pop_front().unwrap();
                if let TokenType::CloseParen = next_token.token_type {
                    return Ok(SyntaxTree::new(SyntaxNode::ParenExpr(Box::new(expr))));
                }

                return Err(ParsingError::UnexpectedToken(next_token));
            }

            _ => Err(ParsingError::UnexpectedToken(next_token))
        }
    }


    /// Produces a monadic action such as `IO<()>` or `IO<str>`.
    /// 
    /// The value contained within a monad cannot be extracted from a monad outside of another
    /// monad, as in Haskell, for example. This ensures that side effects, such as reading and
    /// writing from standard I/O, are properly ordered and are not parallelized, causing problems
    /// with out-of-order effects - this is why monads are never parallelized.
    fn parse_do_block(&mut self) -> Result<SyntaxTree, ParsingError> {
        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::OpenCurly));

        let body = self.parse_stmt_block()?;

        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::CloseCurly));

        Ok(SyntaxTree::new(SyntaxNode::MonadicExpr(body)))
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
                _ => return Err(ParsingError::UnexpectedToken(next_token))
            }
        }

        Ok(args)
    }


    fn parse_selection(&mut self) -> Result<SyntaxTree, ParsingError> {
        // parse the condition
        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::OpenParen));

        let cond = self.parse_expression()?;
        if get_expr_type(&cond, &self.context).unwrap() != Type::new(SimpleType::Bool, false, vec![]) {
            panic!("If statement's condition must be of type bool!");
        }

        let next_token = self.tokens.pop_front().unwrap();
        assert!(matches!(next_token.token_type, TokenType::CloseParen));

        let next_token = self.tokens.pop_front().unwrap();
        let if_body = match next_token.token_type {
            TokenType::OpenCurly => {
                let result = self.parse_stmt_block()?;
                let next_token = self.tokens.pop_front().unwrap();
                assert!(matches!(next_token.token_type, TokenType::CloseCurly));
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
                        assert!(matches!(next_token.token_type, TokenType::CloseCurly));
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

        Ok(SyntaxTree::new(SyntaxNode::SelectionStatement(Box::new(cond), if_body, else_body)))
    }
}
