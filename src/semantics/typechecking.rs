//! # Skopje Typechecking Library
//!
//! This library provides tools for typechecking expressions and function bodies according to
//! Skopje's type system. It focuses on ensuring that expressions conform to expected types and 
//! does not concern itself with computational or runtime types.
//!
//! The library uses the [`TypeField`] to progressively narrow down the possible types an expression
//! may have, and ultimately selects the most appropriate type if multiple are possible. If at any 
//! point the type field for an expression becomes empty, a type error is raised, indicating that 
//! the expression is not well-typed according to the Skopje type system. This error is represented 
//! by the [`TypeError`] type.
//!
//! ## Key Functions
//!
//! - [`get_expr_type`]: Determines the type of a given expression within a specific context.
//! - [`get_l_expr_type`]: Determines the type of an l-value expression, typically an identifier 
//!    or array indexing operation.
//! - [`get_array_inner_type`]: Retrieves the inner type of an array or iterable.
//! - [`is_constexpr`]: Checks if an expression is a constant expression, which can be evaluated 
//!    at compile time.
//! - [`fold_constexpr_index`]: Folds a constant expression into a specific index value.
//!
//! ## Modules and Dependencies
//!
//! This module depends on the following components from the broader codebase:
//!
//! - `parser::parsing`: Provides the `SyntaxNode` and `SyntaxTree` types, which represent 
//!    parsed expressions and function bodies.
//! - `parser::types`: Provides the `Type` and `SimpleType` types, which represent the possible 
//!    types in the Skopje type system.
//! - `errors`: Provides the `TypeError` type, used to represent typechecking errors.
//! - `symbol_table`: Provides the `SymbolTable` and `SymbolType` types, used to manage symbols 
//!    and their types in a given scope.
//!
//! ## Example Usage
//!
//! The functions in this module are typically used during the semantic analysis phase of a 
//! compiler, where the goal is to ensure that all expressions and function bodies are well-typed 
//! according to the rules of the Skopje type system.
//!
//! ```rust
//! use skopje::typechecker::get_expr_type;
//! use skopje::symbol_table::SymbolTable;
//! use skopje::parser::parsing::SyntaxTree;
//!
//! let syntax_tree = ...;  // Assume this is provided from the parser
//! let symbol_table = SymbolTable::new(None);  // Create a new symbol table with no parent
//!
//! match get_expr_type(&syntax_tree, &symbol_table) {
//!     Ok(expr_type) => println!("Expression type: {:?}", expr_type),
//!     Err(e) => eprintln!("Type error: {:?}", e),
//! }
//! ```
use std::borrow::Borrow;
use std::collections::HashMap;
use std::error::Error;

use crate::parser::parsing::{SyntaxNode, SyntaxTree};
use crate::parser::types::{Type, SimpleType};

use super::errors::TypeError;
use super::symbol_table::{SymbolTable, SymbolType};


/// Determines the type of a given expression within a specific context.
///
/// This function recursively evaluates the type of an expression by examining its syntax tree and
/// resolving the types of sub-expressions. If the expression cannot be resolved to a single type,
/// or if there is a type error, the function returns an error.
///
/// # Arguments
///
/// * `expr` - A reference to the `SyntaxTree` representing the expression.
/// * `context` - A reference to the `SymbolTable` providing the current scope's symbol information.
///
/// # Returns
///
/// A `Result` containing the resolved `Type` of the expression, or an error if the type cannot be
/// determined.
pub fn get_expr_type(expr: &SyntaxTree, context: &SymbolTable) -> Result<Type, Box<dyn Error>> {
    match &expr.node {
        SyntaxNode::BinaryOperation(op, l, r) => match op.as_str() {
            ".." => {
                let left_type = get_expr_type(l, context)?;
                let (left_value, right_value) = (fold_constexpr_index(l), fold_constexpr_index(r));
                Ok(Type::from_basic(SimpleType::Array(Box::new(left_type), usize::abs_diff(left_value, right_value))))
            }

            "::" => {
                let left_type = get_expr_type(l, context)?;
                let right_type = get_expr_type(r, context)?;
                match (left_type.basic_type, right_type.basic_type) {
                    (SimpleType::Str, SimpleType::Str) => Ok(Type::from_basic(SimpleType::Str)),
                    (SimpleType::Array(t1, size1), SimpleType::Array(t2, size2)) => {
                        if t1.is_compatible_with(&t2) {
                            return Ok(Type::from_basic(SimpleType::Array(t1, size1 + size2)))
                        } 

                        panic!()
                    }
                    _ => panic!()
                }
            }

            "." => get_struct_member_type(None, expr, context),
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
        SyntaxNode::FloatLiteral(_) => Ok(Type::from_basic(SimpleType::F64)),
        SyntaxNode::StringLiteral(_) => Ok(Type::new(SimpleType::Str, false, vec![])),
        SyntaxNode::BoolLiteral(_) => Ok(Type::new(SimpleType::Bool, false, vec![])),
        SyntaxNode::ParenExpr(expr) => get_expr_type(expr, context),
        SyntaxNode::Identifier(id) => Ok(context.get(id).expect(id).category.get_type()),

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

        SyntaxNode::FunctionCall(id, args) => {
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
            SimpleType::Enum(enum_name, variants, _, _, _) => {
                assert!(variants.contains_key(variant_name));
                Ok(Type::from_basic(SimpleType::Enum(enum_name, variants, Some(variant_name.to_owned()), HashMap::new(), vec![])))
            }
            _ => panic!()
        }

        SyntaxNode::TypeCast(new_type, old_type, _) => {
            assert!(
                old_type.is_numeric() && new_type.is_numeric() 
                || old_type == new_type 
                || old_type.is_numeric() && new_type.basic_type == SimpleType::Bool
                || new_type.is_numeric() && old_type.basic_type == SimpleType::Bool
            );
            Ok(new_type.clone())
        },

        SyntaxNode::SelfIdentifier => {
            match &context.get(&String::from("self")) {
                Some(self_ref) => Ok(self_ref.get_type()),
                None => panic!("Using self is not valid in this context!")
            }
        }

        SyntaxNode::StructInstantiation(name, instance_members) => {
            // check that all the members of the instance are the correct type
            let struct_type: Type = context.get(name).unwrap().get_type();
            match &struct_type.basic_type {
                SimpleType::Struct(_, type_members, _) => {
                    // check that the instance has the right number of members
                    assert_eq!(type_members.len(), instance_members.len());
                    for (m, t) in type_members.iter() {
                        let instance_member_type: Type = get_expr_type(instance_members.get(m).unwrap(), context)?;
                        if !t.is_compatible_with(&instance_member_type) {
                            return Err(Box::new(TypeError::new(vec![t.clone()], instance_member_type)))
                        }
                    }
                }

                _ => panic!()
            };

            Ok(struct_type)
        }

        SyntaxNode::ConcatStr(l, r) => {
            assert_eq!(get_expr_type(l, context).unwrap().basic_type, SimpleType::Str);
            assert_eq!(get_expr_type(r, context).unwrap().basic_type, SimpleType::Str);
            Ok(Type::from_basic(SimpleType::Str))
        }

        SyntaxNode::TernaryExpression(cond, if_true, if_false) => {
            let if_true_type = get_expr_type(if_true.borrow(), context)?;
            let if_false_type = get_expr_type(if_false.borrow(), context)?;
            assert_eq!(get_expr_type(cond.borrow(), context)?, Type::from_basic(SimpleType::Bool));
            assert!(if_true_type.is_compatible_with(&if_false_type));
            Ok(if_true_type)
        }

        SyntaxNode::MonadicExpr(_, Some((_, param_t)), rt) => 
            Ok(Type::new(SimpleType::IOMonad(Box::new(rt.clone()), Some(Box::new(param_t.clone()))), false, vec![rt.clone()])),
        SyntaxNode::MonadicExpr(_, None, rt) => 
            Ok(Type::new(SimpleType::IOMonad(Box::new(rt.clone()), None), false, vec![rt.clone()])),
        other => unimplemented!("Have not yet implemented {:?}", other)
    }
}


pub fn get_monad_return_type(tree: &SyntaxTree, context: &SymbolTable) -> Option<Type> {
    match &tree.node {
        SyntaxNode::ForStmt(_, _, _, body) 
        | SyntaxNode::WhileStmt(_, body) => get_monad_return_type(body, context),

        SyntaxNode::ReturnStmt(expr) => {
            match get_expr_type(&expr, context) {
                Ok(t) => Some(t),
                Err(e) => panic!("{:?}", e)
            }
        }

        SyntaxNode::StmtBlock(body, new_context) => {
            let mut rt: Option<Type> = None;
            for stmt in body {
                let new_type = get_monad_return_type(stmt, &(**new_context).borrow());
                if rt.is_none() {
                    rt = new_type;
                    continue;
                }

                if !new_type.is_none() && !rt.is_none() && !new_type.unwrap().is_compatible_with(&rt.clone().unwrap()) {
                    panic!()
                }
            }

            rt
        },

        SyntaxNode::SelectionStatement(_, if_body, else_body) => {
            let rt = get_monad_return_type(if_body, context);
            match &**else_body {
                Some(tree) => {
                    let else_return = get_monad_return_type(tree, context);
                    if else_return.is_some() {
                        match &rt {
                            Some(rt) => { else_return.unwrap().is_compatible_with(&rt); },
                            None => return else_return
                        } 
                    }

                    rt
                }
                None => None
            }
        }

        SyntaxNode::MatchStmt(_, patterns, _) => {
            let mut rt: Option<Type> = None;
            for (_, tree) in patterns {
                let new_type = get_monad_return_type(tree, context);
                if rt.is_none() {
                    rt = new_type;
                    continue;
                }

                if !new_type.is_none() && !rt.is_none() && !new_type.unwrap().is_compatible_with(&rt.clone().unwrap()) {
                    panic!()
                }
            }

            rt
        }

        _ => None
    }
}


fn get_struct_member_type(right_type: Option<Type>, l: &SyntaxTree, context: &SymbolTable) -> Result<Type, Box<dyn Error>> {
    // if the right type is num, make the right type be the type of l
    let right_type: Type = match right_type {
        None => match &l.node {
            SyntaxNode::BinaryOperation(_, left, right) => {
                let left_type = match &left.node {
                    SyntaxNode::Identifier(id) => context.get(&id).expect(id).get_type(),
                    SyntaxNode::SelfIdentifier => context.get(&String::from("self")).unwrap().get_type(),
                    SyntaxNode::BinaryOperation(_, _, _) => get_struct_member_type(None, left, context)?,
                    SyntaxNode::ArrayIndexingOperation(_, array) => get_array_inner_type(&get_expr_type(array, context)?),
                    other => panic!("Expected identifier, got {:?}", other)
                };
                return get_struct_member_type(Some(left_type), &right, context);
            }
            
            _ => panic!()
        },
        
        Some(l) => l
    };
    
    match &l.node {
        SyntaxNode::Identifier(id) => match right_type.basic_type {
            SimpleType::Struct(_, members, _) => Ok(members.get(id).unwrap().clone()),
            _ => panic!()
        }

        SyntaxNode::FunctionCall(name, _) => match right_type.basic_type {
            SimpleType::Struct(_, _, methods) | SimpleType::Enum(_, _, _, methods, _) => {
                match &methods.get(name).unwrap().basic_type {
                    SimpleType::Function(rt, _) => Ok(*rt.clone()),
                    other => panic!("{:?}", other)
                }
            }
            _ => Ok(right_type.clone())
        }

        SyntaxNode::BinaryOperation(op, left, right) => {
            if op.as_str() != "." {
                panic!("Expected '.' operator, got {}", op);
            }

            let right_type = get_expr_type(&right, context)?;
            println!("right_type: {:?}", right_type);
            get_struct_member_type(Some(right_type), left, context)
        }

        SyntaxNode::ArrayIndexingOperation(_, array) => Ok(get_array_inner_type(&get_expr_type(array, context)?)),

        other => panic!("Got {:?}", other)
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

        "." => {
            match l_type.basic_type {
                SimpleType::Enum(_, _, _, behaviours, _) => 
                    get_enum_expr_return_type(behaviours, r, context),
                _ => panic!()
            }
        }

        "==" | "!=" => {
            if l_type.is_compatible_with(&r_type) {
                return Ok(Type::from_basic(SimpleType::Bool))
            }

            Err(Box::new(TypeError::new(vec![l_type], r_type)))
        }

        "->" => {
            if l_type.is_compatible_with(&r_type) {
                return Ok(l_type)
            }

            match &r_type.basic_type {
                SimpleType::IOMonad(_, Some(param)) => {
                    if l_type.is_compatible_with(&*param) {
                        return Ok(Type::from_basic(SimpleType::IOMonad(Box::new(l_type), None)));
                    }
                    Err(Box::new(TypeError::new(vec![l_type], r_type)))
                }
                _ => Err(Box::new(TypeError::new(vec![l_type], r_type)))
            }
        }

        _ => panic!("Did not recognise operator {}", op)
    }
} 


fn get_enum_expr_return_type(behaviours: HashMap<String, Box<Type>>, tree: &SyntaxTree, context: &SymbolTable) -> Result<Type, Box<dyn Error>> {
    let mut behaviours = behaviours;
    match &tree.node {
        SyntaxNode::BinaryOperation(op, left, right) => {
            if op.as_str() != "." {
                panic!("Expected '.' operator, got {}", op)
            }

            let l_type: Type = get_expr_type(left, context)?;
            match l_type.basic_type {
                SimpleType::Enum(_, _, _, new_behaviours, _) => {
                    behaviours.extend(new_behaviours);
                    get_enum_expr_return_type(behaviours, right, context)
                }
                _ => panic!()
            }
        }

        other => panic!("Expected identifier or '.', got {:?}", other)
    }
}


/// Determines the type of an l-value expression, such as an identifier or array indexing operation.
///
/// This function is used specifically for expressions that can appear on the left-hand side of an
/// assignment, such as variables or elements of an array.
///
/// # Arguments
///
/// * `expr` - A reference to the `SyntaxTree` representing the l-expression.
/// * `symbol_table` - A reference to the `SymbolTable` providing the current scope's symbol 
/// information.
///
/// # Returns
///
/// A `Result` containing the resolved `Type` of the l-expression, or an error if the type cannot be
/// determined.
pub fn get_l_expr_type(expr: &SyntaxTree, symbol_table: &SymbolTable) -> Result<Type, Box<dyn Error>> {
    match &expr.node {
        SyntaxNode::Identifier(id) => Ok(symbol_table.get(id).unwrap().get_type()),
        SyntaxNode::ArrayIndexingOperation(_, expr) => Ok(get_array_inner_type(&get_l_expr_type(expr, symbol_table).unwrap())),
        SyntaxNode::BinaryOperation(op, l, r) => {
            assert_eq!(op.as_str(), ".");
            let right_id = match &r.node {
                SyntaxNode::Identifier(id) => id,
                other => panic!("Expected identifier, got {:?}", other)
            };

            let left_type = get_l_expr_type(l, symbol_table)?;
            match left_type.basic_type {
                SimpleType::Struct(_, members, _) => Ok(members.get(right_id).unwrap().clone()),
                _ => panic!()
            }
        }

        other => panic!("Invalid node {:?} in l-expression", other)
    }
}


pub fn get_function_type(func: &SyntaxTree) -> Type {
    match &func.node {
        SyntaxNode::Function(_, args, rt, _) => {
            let arg_types = args.iter().map(|(_, t)| t).cloned().collect();
            Type::new(SimpleType::Function(Box::new(rt.clone()), arg_types), false, vec![])
        }
        _ => panic!()
    }
}


/// Retrieves the inner type of an array or iterable type.
///
/// This function extracts the type of the elements contained within an array or iterator. It is
/// useful for operations that need to manipulate or access the elements of a collection.
///
/// # Arguments
///
/// * `array` - A reference to the `Type` representing the array or iterable.
///
/// # Returns
///
/// The `Type` of the elements contained within the array or iterable.
pub fn get_array_inner_type(array: &Type) -> Type {
    match &array.basic_type {
        SimpleType::Array(inner, _) 
        | SimpleType::Iterator(inner) => *inner.clone(),
        other => panic!("Expected array, got {:?}", other)
    }
}


/// Checks if an expression is a constant expression, which can be evaluated at compile time.
///
/// A constant expression is one that can be fully resolved without runtime information. This 
/// function is typically used to verify whether certain operations or optimizations can be applied 
/// at compile time.
///
/// # Arguments
///
/// * `expr` - A reference to the `SyntaxTree` representing the expression.
///
/// # Returns
///
/// `true` if the expression is a constant expression, otherwise `false`.
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


/// Folds a constant expression into a specific index value.
///
/// This function reduces a constant expression to its corresponding index value, which is typically
/// used for operations like array indexing or tuple indexing.
///
/// # Arguments
///
/// * `expr` - A reference to the `SyntaxTree` representing the constant expression.
///
/// # Returns
///
/// The index value as a `usize`.
///
/// # Panics
///
/// This function will panic if the expression is not a valid constant expression or cannot be 
/// reduced to a single index value.
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
        let scanner = Scanner::new("tests/should_pass/test_basic_integer_checking.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    fn test_tuples() {
        let scanner = Scanner::new("tests/should_pass/test_tuples.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    fn test_basic_array() {
        let scanner = Scanner::new("tests/should_pass/test_basic_array.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    fn test_multidimensional_array() {
        let scanner = Scanner::new("tests/should_pass/test_multidimensional_array.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    fn test_basic_enum() {
        let scanner = Scanner::new("tests/should_pass/test_basic_enum.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_malformed_tuple() {
        let scanner = Scanner::new("tests/should_fail/test_malformed_tuple.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_non_constexpr_tuple_index() {
        let scanner = Scanner::new("tests/should_fail/test_non_constexpr_tuple_index.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_heterogenous_array() {
        let scanner = Scanner::new("tests/should_fail/test_heterogenous_array.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_ill_typed_array() {
        let scanner = Scanner::new("tests/should_fail/test_ill_typed_array.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_for_loop_no_array() {
        let scanner = Scanner::new("tests/should_fail/test_for_loop_no_array.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_for_loop_inconsistent_iter_type() {
        let scanner = Scanner::new("tests/should_fail/test_for_loop_inconsistent_iter_type.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_enum_without_variant() {
        let scanner = Scanner::new("tests/should_fail/test_enum_without_variant.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        parser.parse().unwrap();
    }
}
