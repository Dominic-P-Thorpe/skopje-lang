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

use super::errors::TypeError;
use super::symbol_table::{SymbolTable, SymbolType};


pub fn get_expr_type(expr: &SyntaxTree, context: &SymbolTable) -> Result<Type, Box<dyn Error>> {
    match &expr.node {
        SyntaxNode::BinaryOperation(op, l, r) => match op.as_str() {
            ".." => {
                let left_type = get_expr_type(l, context)?;
                let (left_value, right_value) = (fold_constexpr_index(l), fold_constexpr_index(r));
                Ok(Type::from_basic(SimpleType::Array(Box::new(left_type), usize::abs_diff(left_value, right_value))))
            }
            _ => get_binary_operation_type(op.to_string(), &*l, &*r, context)
        }

        SyntaxNode::LeftAssocUnaryOperation(op, arg)
        | SyntaxNode::RightAssocUnaryOperation(op, arg) => get_unary_operation_type(
            op.to_string(), 
            get_expr_type(&*arg, context)?
        ),

        SyntaxNode::SubarrayOperation(root, _, start, end) => {
            let root_type = get_expr_type(&root, context)?;
            match &root_type.basic_type {
                SimpleType::Array(inner_type, _) => 
                    Ok(Type::from_basic(SimpleType::Array(inner_type.clone(), end - start))),
                other => panic!("Expected array, got {:?}", other)
            }
        }

        SyntaxNode::IntLiteral(_) => Ok(Type::new(SimpleType::I64, false, vec![])),
        SyntaxNode::StringLiteral(_) => Ok(Type::new(SimpleType::Str, false, vec![])),
        SyntaxNode::BoolLiteral(_) => Ok(Type::new(SimpleType::Bool, false, vec![])),
        SyntaxNode::ParenExpr(expr) => get_expr_type(expr, context),
        SyntaxNode::Identifier(id) => Ok(context.get(id).unwrap().category.get_type()),

        SyntaxNode::TupleIndexingOperation(index, expr) => {
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

        SyntaxNode::ArrayIndexingOperation(_, expr) => {
            match get_expr_type(expr, context)?.basic_type {
                SimpleType::Array(inner, _) => Ok(*inner),
                other => panic!("Expected array, got {:?}", other)
            }
        }

        SyntaxNode::FunctionCall(id, args) 
        | SyntaxNode::FunctionCallStmt(id, args)=> {
            let (func_return_type, param_types) = match context.get(&id).unwrap().category {
                SymbolType::Function(_, func_type) => match func_type.basic_type {
                    SimpleType::Function(rt, params) => (*rt, params),
                    other => panic!("Expected function, got {:?}", other)
                }
                _ => panic!()
            };

            // check that there are the correct number of arguments for the given function
            if param_types.len() != args.len() {
                panic!("Expected {} arguments for function {}, got {}", param_types.len(), id, args.len())
            }

            // verify that the parameters are all of the same type
            for i in 0..param_types.len() {
                let arg_type: Type = get_expr_type(args.get(i).unwrap(), context)?;
                let param_type: &Type = param_types.get(i).unwrap();
                if !arg_type.is_compatible_with(param_type) {
                    return Err(Box::new(TypeError::new(vec![arg_type], param_type.clone())));
                }
            }

            Ok(func_return_type)
        }

        SyntaxNode::TupleLiteral(exprs) => {
            let types: Vec<Type> = exprs.iter().map(|e| get_expr_type(e, context).unwrap()).collect();
            Ok(Type::new(SimpleType::Tuple(types), false, vec![]))
        }

        SyntaxNode::ArrayLiteral(elems, inner_type) => {
            for elem in elems {
                let elem_type = get_expr_type(elem, context)?;
                if !elem_type.is_compatible_with(&inner_type) {
                    return Err(Box::new(TypeError::new(vec![inner_type.clone()], elem_type)));
                }
            }

            Ok(Type::new(SimpleType::Array(Box::new(inner_type.clone()), elems.len()), false, vec![]))
        }

        SyntaxNode::EnumInstantiation(enum_type, variant_name, _) => match enum_type.basic_type.clone() {
            SimpleType::Enum(enum_name, variants, _) => {
                assert!(variants.contains_key(variant_name));
                Ok(Type::from_basic(SimpleType::Enum(enum_name, variants, Some(variant_name.to_owned()))))
            }
            _ => panic!()
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


fn get_binary_operation_type(op: String, l: &SyntaxTree, r: &SyntaxTree, context: &SymbolTable) -> Result<Type, Box<dyn Error>> {
    let l_type: Type = get_expr_type(l, context)?;
    let r_type: Type = get_expr_type(r, context)?;
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

        ".." => {
            if l_type.is_numeric() && r_type.is_numeric() && is_constexpr(l) && is_constexpr(r) {
                Ok(Type::new(SimpleType::Array(Box::new(l_type), usize::abs_diff(fold_constexpr_index(r), fold_constexpr_index(l))), false, vec![]))
            } else {
                panic!("Expected numerical types for operation {}, got {:?}", op, l_type)
            }
        }

        // 2 array arguments and an array result
        "::" => {
            if let SimpleType::Array(l_inner, l_size) = l_type.basic_type {
                if let SimpleType::Array(r_inner, r_size) = r_type.basic_type {
                    if !l_inner.is_compatible_with(&r_inner) {
                        panic!("{:?} is not compatible with {:?}!", l_inner, r_inner);
                    }
                    return Ok(Type::new(SimpleType::Array(l_inner, l_size + r_size), false, vec![]))
                }
            }

            panic!("Expected 2 array arguments for operation ::")
        }

        "==" | "!=" => unimplemented!("Have not yet implemented equality!"),
        _ => panic!("Did not recognise operator {}", op)
    }
} 


/// Gets the type of an l-expression, which is composed of an identifier and potentially any
/// number of array index operations.
pub fn get_l_expr_type(expr: &SyntaxTree, symbol_table: &SymbolTable) -> Result<Type, Box<dyn Error>> {
    match &expr.node {
        SyntaxNode::Identifier(id) => Ok(symbol_table.get(id).unwrap().get_type()),
        SyntaxNode::ArrayIndexingOperation(_, expr) => Ok(get_array_inner_type(&get_l_expr_type(expr, symbol_table).unwrap())),
        other => panic!("Invalid node {:?} in l-expression", other)
    }
}


pub fn get_array_inner_type(array: &Type) -> Type {
    match &array.basic_type {
        SimpleType::Array(inner, _) 
        | SimpleType::Iterator(inner) => *inner.clone(),
        other => panic!("Expected array, got {:?}", other)
    }
}


pub fn is_constexpr(expr: &SyntaxTree) -> bool {
    match &expr.node {
        SyntaxNode::BinaryOperation(_, l, r) => is_constexpr(&l.clone()) && is_constexpr(&r.clone()),
        SyntaxNode::LeftAssocUnaryOperation(_, l) => is_constexpr(&l.clone()),
        SyntaxNode::RightAssocUnaryOperation(_, r) => is_constexpr(&r.clone()),
        SyntaxNode::ParenExpr(expr) => is_constexpr(&expr.clone()),
        SyntaxNode::TupleIndexingOperation(index, expr) => is_constexpr(&index.clone()) && is_constexpr(&expr.clone()),
        SyntaxNode::TernaryExpression(c, t, f) => is_constexpr(&c.clone()) && is_constexpr(&t.clone()) && is_constexpr(&f.clone()),
        SyntaxNode::IntLiteral(_) 
        | SyntaxNode::BoolLiteral(_) 
        | SyntaxNode::StringLiteral(_) 
        | SyntaxNode::TupleLiteral(_) => true,
        _ => false
    }
}


pub fn fold_constexpr_index(expr: &SyntaxTree) -> usize {
    match expr.node {
        SyntaxNode::IntLiteral(i) => i as usize,
        _ => panic!("Could not fold constexpr!")
    }
}


#[cfg(test)]
mod tests {
    use crate::parser::parsing::Parser;
    use crate::parser::lexing::Scanner;
    use crate::parser::types::{Type, SimpleType};


    #[test]
    fn test_array_compatibility() {
        assert!(
            Type::new(SimpleType::Array(Box::new(Type::new(SimpleType::I32, false, vec![])), 5), false, vec![])
                .is_compatible_with(&Type::new(SimpleType::Array(Box::new(Type::new(SimpleType::I64, false, vec![])), 5), false, vec![])),
        );

        assert!(
            Type::new(SimpleType::Array(Box::new(Type::new(SimpleType::I64, false, vec![])), 5), false, vec![])
                .is_compatible_with(&Type::new(SimpleType::Array(Box::new(Type::new(SimpleType::I32, false, vec![])), 5), false, vec![])),
        )
    }


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
    fn test_basic_array() {
        let scanner = Scanner::new("tests/test_basic_array.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        parser.parse().unwrap();
    }


    #[test]
    fn test_multidimensional_array() {
        let scanner = Scanner::new("tests/test_multidimensional_array.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        parser.parse().unwrap();
    }


    #[test]
    fn test_basic_enum() {
        let scanner = Scanner::new("tests/test_basic_enum.skj").unwrap();
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


    #[test]
    #[should_panic]
    fn test_heterogenous_array() {
        let scanner = Scanner::new("tests/test_heterogenous_array.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_ill_typed_array() {
        let scanner = Scanner::new("tests/test_ill_typed_array.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_for_loop_no_array() {
        let scanner = Scanner::new("tests/test_for_loop_no_array.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_for_loop_inconsistent_iter_type() {
        let scanner = Scanner::new("tests/test_for_loop_inconsistent_iter_type.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_enum_without_variant() {
        let scanner = Scanner::new("tests/test_enum_without_variant.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        parser.parse().unwrap();
    }
}
