//! This library is for typechecking expressions and function bodies according to Skopje's typing
//! system - it does not concern itself with computational types.
//! 
//! Uses [`TypeField`] to steadily narrow down the possible types and expression may have and then,
//! at the end, will pick the best if it is not clear. If at any point the type field for an
//! expression is empty, then no progress can be made and the expression has a type error (which is
//! implemented as [`TypeError`]).
use std::error::Error;

use crate::parser::parsing::{SyntaxNode, SyntaxTree};
use crate::parser::types::{Type, SimpleType};
use crate::Context;

use super::errors::TypeError;


pub fn get_expr_type(expr: &SyntaxTree, context: &Context) -> Result<Type, Box<dyn Error>> {
    match &expr.node {
        SyntaxNode::BinaryOperation(op, l, r) => get_binary_operation_type(
            op.to_string(), 
            get_expr_type(&*l, context)?, 
            get_expr_type(&*r, context)?
        ),

        SyntaxNode::LeftAssocUnaryOperation(op, arg)
        | SyntaxNode::RightAssocUnaryOperation(op, arg) => get_unary_operation_type(
            op.to_string(), 
            get_expr_type(&*arg, context)?
        ),

        SyntaxNode::IntLiteral(_) => Ok(Type::new(SimpleType::I64, false, vec![])),
        SyntaxNode::StringLiteral(_) => Ok(Type::new(SimpleType::Str, false, vec![])),
        SyntaxNode::BoolLiteral(_) => Ok(Type::new(SimpleType::Bool, false, vec![])),
        SyntaxNode::Identifier(id) => Ok(context.valid_identifiers.get(id).unwrap().0.clone()),
        SyntaxNode::ParenExpr(expr) => get_expr_type(expr, context),

        SyntaxNode::IndexingOperation(index, expr) => {
            match get_expr_type(expr, context).unwrap().basic_type {
                SimpleType::Tuple(types) => {
                    if !is_constexpr(index) {
                        panic!("Indexing operation on a tuple must have a constexpr index!");
                    }
                    Ok(types.get(fold_constexpr_index(index)).unwrap().clone())
                }
                t => panic!("Cannot use indexing operation on type {:?}", t)
            }
        }

        SyntaxNode::FunctionCall(id, args) 
        | SyntaxNode::FunctionCallStmt(id, args)=> {
            let (func_return_type, param_types) = match context.verify_function(&id) {
                Some(f) => match f.basic_type {
                    SimpleType::Function(rt, params) => (*rt, params),
                    other => panic!("Expected function, got {:?}", other)
                },
                None => panic!("Identifier {} is not valid in this context", id)
            };

            // check that there are the correct number of arguments for the given function
            if param_types.len() != args.len() {
                panic!("Expected {} arguments for function {}, got {}", param_types.len(), id, args.len())
            }

            // verify that the parameters are all of the same type
            for i in 0..param_types.len() {
                let arg_type: Type = get_expr_type(args.get(i).unwrap(), context)?;
                let param_type: &Type = param_types.get(i).unwrap();
                if &arg_type != param_type {
                    return Err(Box::new(TypeError::new(vec![arg_type], param_type.clone())));
                }
            }

            Ok(func_return_type)
        }

        SyntaxNode::TupleLiteral(exprs) => {
            let types: Vec<Type> = exprs.iter().map(|e| get_expr_type(e, context).unwrap()).collect();
            Ok(Type::new(SimpleType::Tuple(types), false, vec![]))
        }

        other => unimplemented!("Have not yet implemented {:?}", other)
    }
}


fn get_unary_operation_type(op: String, arg: Type) -> Result<Type, Box<dyn Error>> {
    match op.as_str() {
        "-" | "+" | "~" | "++" | "--" => {
            if arg.is_numeric() {
                Ok(arg)
            } else {
                Err(Box::new(TypeError::new(vec![
                    Type::new(SimpleType::I64, false, vec![]),
                    Type::new(SimpleType::U64, false, vec![])
                ], arg)))
            }
        },

        "!" => {
            if let SimpleType::Bool = arg.basic_type {
                Ok(Type::new(SimpleType::Bool, false, vec![]))
            } else {
                Err(Box::new(TypeError::new(vec![
                    Type::new(SimpleType::Bool, false, vec![])
                ], arg)))
            }
        },

        _ => todo!()
    }
}


fn get_binary_operation_type(op: String, l_type: Type, r_type: Type) -> Result<Type, Box<dyn Error>> {
    match op.as_str() {
        // two numerical arguments and a numerical output
        "+" | "-" | "*" | "/" | "**" | "%" | "&" | "|" | ">>" | ">>>" | "<<" => {
            if l_type.is_numeric() && r_type.is_numeric() {
                Ok(l_type)
            } else {
                panic!("Expected numerical types for operation {}, got {:?}", op, l_type)
            }
        }

        // two boolean arguments and a boolean output
        "&&" | "||" => {
            if l_type == Type::new(SimpleType::Bool, false, vec![]) && r_type == Type::new(SimpleType::Bool, false, vec![]) {
                Ok(l_type)
            } else {
                panic!("Expected boolean types for operation {}, got {:?}", op, l_type)
            }
        },

        ">" | "<" | ">=" | "<=" => {
            if l_type.is_numeric() && r_type.is_numeric() {
                Ok(Type::new(SimpleType::Bool, false, vec![]))
            } else {
                panic!("Expected numerical types for operation {}, got {:?}", op, l_type)
            }
        },

        "==" | "!=" => unimplemented!("Have not yet implemented equality!"),
        _ => panic!("Did not recognise operator {}", op)
    }
} 


fn is_constexpr(expr: &SyntaxTree) -> bool {
    match &expr.node {
        SyntaxNode::BinaryOperation(_, l, r) => is_constexpr(&l.clone()) && is_constexpr(&r.clone()),
        SyntaxNode::LeftAssocUnaryOperation(_, l) => is_constexpr(&l.clone()),
        SyntaxNode::RightAssocUnaryOperation(_, r) => is_constexpr(&r.clone()),
        SyntaxNode::ParenExpr(expr) => is_constexpr(&expr.clone()),
        SyntaxNode::IndexingOperation(index, expr) => is_constexpr(&index.clone()) && is_constexpr(&expr.clone()),
        SyntaxNode::TernaryExpression(c, t, f) => is_constexpr(&c.clone()) && is_constexpr(&t.clone()) && is_constexpr(&f.clone()),
        SyntaxNode::IntLiteral(_) 
        | SyntaxNode::BoolLiteral(_) 
        | SyntaxNode::StringLiteral(_) 
        | SyntaxNode::TupleLiteral(_) => true,
        _ => false
    }
}


fn fold_constexpr_index(expr: &SyntaxTree) -> usize {
    match expr.node {
        SyntaxNode::IntLiteral(i) => i as usize,
        _ => panic!("Could not fold constexpr!")
    }
}


#[cfg(test)]
mod tests {
    use crate::parser::parsing::Parser;
    use crate::parser::lexing::Scanner;


    #[test]
    fn test_basic_integer_checking() {
        let scanner = Scanner::new("tests/test_basic_integer_checking.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        parser.parse().unwrap();
    }


    #[test]
    fn test_tuples() {
        let scanner = Scanner::new("tests/test_tuples.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_malformed_tuple() {
        let scanner = Scanner::new("tests/test_malformed_tuple.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_non_constexpr_tuple_index() {
        let scanner = Scanner::new("tests/test_non_constexpr_tuple_index.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        parser.parse().unwrap();
    }
}
