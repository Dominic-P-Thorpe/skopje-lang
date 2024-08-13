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


/// Used to denote a set of possible types that something may have. For example, we may know that 
/// an expression has a numeric type, but not precicely which numeric type.
/// 
/// # Example
/// 
/// ```
/// let type_field: TypeField = TypeField::new();
/// ```
#[derive(Debug, Clone)]
pub struct TypeField {
    valid_types: Vec<Type>
}


#[allow(unused)]
impl TypeField {
    /// Creates a new [`TypeField`] instance where the valid types are all the possible types
    /// available in the given context of the program. 
    pub fn new() -> Self {
        TypeField {
            valid_types: vec![
                Type::new(SimpleType::I32, false, vec![]).unwrap(),
                Type::new(SimpleType::U32, false, vec![]).unwrap(),
                Type::new(SimpleType::Str, false, vec![]).unwrap(),
                Type::new(SimpleType::Bool, false, vec![]).unwrap(),
            ]
        }
    }


    /// Creates a new [`TypeField`] instance where the valid types are all the possible 
    /// <b>numerical</b> types available in the given context of the program. 
    pub fn new_numeric() -> Self {
        let mut field = Self::new();
        field.restrict_numeric();
        field
    }


    pub fn from_type(t: Type) -> Self {
        TypeField {
            valid_types: vec![t]
        }
    }


    /// Removes all non_numerical types from the valid types in this instance of [`TypeField`].
    pub fn restrict_numeric(&mut self) {
        self.valid_types = self.valid_types
                               .iter()
                               .filter(|t| type_is_numeric(t))
                               .cloned()
                               .collect();
    } 


    /// Adds the given type to the set of valid types
    pub fn add(&mut self, new_type: Type) {
        self.valid_types.push(new_type);
    }


    /// Removes the given type from the set of valid types
    pub fn remove(&mut self, to_remove: &Type) {
        self.valid_types = self.valid_types
                               .iter()
                               .filter(|t| *t != to_remove)
                               .cloned()
                               .collect();
    }


    /// Removes all values from the set of valid types
    pub fn clear(&mut self) {
        self.valid_types = vec![];
    }


    /// True if the set of valid types is empty, otherwise returns false
    pub fn is_empty(&self) -> bool {
        self.valid_types.is_empty()
    }


    /// Returns a new [`TypeField`] containing only those types present in the sets of valid types
    /// of both this type field and the passed type field.
    pub fn intersection(&self, other: &Self) -> Self {
        let intersection = self.valid_types
                               .iter()
                               .filter(|t| other.valid_types.contains(t))
                               .cloned()
                               .collect();
        TypeField { valid_types: intersection }
    }


    /// True if this type field contains the passed type, otherwise false
    pub fn contains(&self, other: &Type) -> bool {
        self.valid_types.contains(other)
    }


    /// True if there is any numerical type in the current set of valid types, otherwise false
    pub fn contains_numeric(&self) -> bool {
        self.valid_types.iter()
            .filter(|t| type_is_numeric(t))
            .cloned()
            .collect::<Vec<Type>>()
            .len() > 0
    }
}


pub fn get_expr_type(expr: &SyntaxTree, context: &Context) -> Result<TypeField, Box<dyn Error>> {
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

        SyntaxNode::IntLiteral(_) => {
            let mut type_field = TypeField::new();
            type_field.restrict_numeric();
            Ok(type_field)
        }

        SyntaxNode::StringLiteral(_) => {
            let mut type_field = TypeField::new();
            type_field.clear();
            type_field.add(Type::new(SimpleType::Str, false, vec![])?);
            Ok(type_field)
        },

        SyntaxNode::BoolLiteral(_) => {
            let mut type_field = TypeField::new();
            type_field.clear();
            type_field.add(Type::new(SimpleType::Bool, false, vec![])?);
            Ok(type_field)
        }

        SyntaxNode::Identifier(id) => {
            let mut type_field = TypeField::new();
            type_field.clear();
            type_field.add(context.valid_identifiers.get(id).unwrap().0.clone());
            Ok(type_field)
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
                let arg_field: TypeField = get_expr_type(args.get(i).unwrap(), context)?;
                let param_type: &Type = param_types.get(i).unwrap();
                if !arg_field.contains(param_type) {
                    return Err(Box::new(TypeError::new(arg_field, TypeField::from_type(param_type.clone()))));
                }
            }

            Ok(TypeField::from_type(func_return_type))
        }

        _ => todo!()
    }
}


fn get_unary_operation_type(op: String, arg: TypeField) -> Result<TypeField, Box<dyn Error>> {
    match op.as_str() {
        "-" | "+" | "~" | "++" | "--" => {
            arg.clone().restrict_numeric();
            Ok(arg)
        },

        "!" => {
            let mut valid_field = TypeField::new();
            valid_field.clear();
            valid_field.add(Type::new(SimpleType::Bool, false, vec![]).unwrap());

            match arg.contains(&Type::new(SimpleType::Bool, false, vec![]).unwrap()) {
                true => Ok(arg.clone()),
                false => Err(Box::new(TypeError::new(valid_field, arg)))
            }
        },

        _ => todo!()
    }
}


fn get_binary_operation_type(op: String, l_type: TypeField, r_type: TypeField) -> Result<TypeField, Box<dyn Error>> {
    let intersection: TypeField = l_type.intersection(&r_type);
    match op.as_str() {
        // two numerical arguments and a numerical output
        "+" | "-" | "*" | "/" | "**" | "%" | "&" | "|" | ">>" | ">>>" | "<<" => {
            match intersection.contains_numeric() {
                true => Ok(intersection),
                false => Err(Box::new(TypeError::new(TypeField::new_numeric(), intersection)))
            }
        }

        // two boolean arguments and a boolean output
        "&&" | "||" => {
            let mut valid_field = TypeField::new();
            valid_field.clear();
            valid_field.add(Type::new(SimpleType::Bool, false, vec![]).unwrap());

            match intersection.contains(&Type::new(SimpleType::Bool, false, vec![]).unwrap()) {
                true => Ok(intersection),
                false => Err(Box::new(TypeError::new(valid_field, intersection)))
            }
        },

        ">" | "<" | ">=" | "<=" => {
            let mut valid_field = TypeField::new();
            valid_field.clear();
            valid_field.add(Type::new(SimpleType::Bool, false, vec![]).unwrap());

            match intersection.contains_numeric() {
                true => Ok(valid_field),
                false => Err(Box::new(TypeError::new(TypeField::new_numeric(), intersection)))
            }
        },

        "==" | "!=" => unimplemented!("Have not yet implemented equality!"),
        _ => panic!("Did not recognise operator {}", op)
    }
}


fn type_is_numeric(t: &Type) -> bool {
    match t.basic_type {
        SimpleType::I32
        | SimpleType::U32 => true,
        _ => false
    }
}
