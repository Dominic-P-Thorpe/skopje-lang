use indexmap::IndexMap;
use std::{collections::HashMap, error::Error};

use crate::semantics::symbol_table::{Symbol, SymbolTable};

use super::errors::ParsingError;

#[derive(Debug, Clone, PartialEq)]
pub enum SimpleType {
    I32,
    I64,
    U32,
    U64,
    Str,
    Void,
    Bool,
    Tuple(Vec<Type>),
    Array(Box<Type>, usize), // inner type, array size
    Iterator(Box<Type>), // inner type
    Function(Box<Type>, Vec<Type>), // return type, vec of params
    // name of the enum, hashmap of names of variants to their members, which are composed of a 
    // member number used to construct an instance of the enum of that member, and a hashmaps of 
    // data members to their types, an option to denote which, if any, variant this enum type is of,
    // a hashmap of behvaiour names to the behaviour, and a vector of traits the enum  inherits
    Enum(String, IndexMap<String, IndexMap<String, Type>>, Option<String>, HashMap<String, Symbol>, Vec<Type>),
    IOMonad
}


impl SimpleType {
    pub fn from_string(src: &str, symbol_table: &SymbolTable) -> Result<Self, Box<dyn Error>> {
        Ok(match src {
            "i32" => Self::I32,
            "i64" => Self::I64,
            "u32" => Self::U32,
            "u64" => Self::U64,
            "str" => Self::Str,
            "void" => Self::Void,
            "bool" => Self::Bool,
            "IO" => Self::IOMonad,
            name => {
                match symbol_table.get(&name.to_owned()) {
                    Some(t) => t.get_type().basic_type,
                    None => return Err(Box::new(ParsingError::InvalidTypeName(name.to_owned()))) 
                }
            }
        })
    }


    /// Converts Skopje types to their closest equivalents in C using the stdint.h library.
    pub fn as_ctype_str(&self) -> String {
        match self {
            Self::Void => String::from("void"),
            Self::I32 => String::from("int32_t"),
            Self::I64 => String::from("int64_t"),
            Self::U32 => String::from("uint32_t"),
            Self::U64 => String::from("uint64_t"),
            Self::Str => String::from("std::string"),
            Self::Bool => String::from("bool"),
            Self::IOMonad => String::from("IOMonad"),
            Self::Iterator(inner) => format!("std::vector<{}>", inner.as_ctype_str()),
            Self::Array(inner_type, size) => format!("std::array<{}, {}>", inner_type.as_ctype_str(), size),
            Self::Tuple(types) => format!(
                "std::tuple<{}>",
                types.iter().map(|t| t.as_ctype_str()).collect::<Vec<String>>().join(", ")
            ),

            Self::Function(return_type, params) => format!(
                "std::function<{}({})>",
                return_type.as_ctype_str(),
                params.iter().map(|p| p.as_ctype_str()).collect::<Vec<String>>().join(", ")
            ),

            Self::Enum(name, _, _, _, _) => name.to_string()
        }
    }


    pub fn is_compatible_with(&self, other: &Self) -> bool {
        if self == other || (self.is_numeric() && other.is_numeric()) {
            return true;
        }

        if let Self::Tuple(this_elems) = self {
            if let Self::Tuple(other_elems) = other {
                // tuples incompatible due to differing sizes
                if this_elems.len() != other_elems.len() {
                    return false;
                }

                // check that all the member elements' types are compatible
                for i in 0..this_elems.len() {
                    if !this_elems.get(i).unwrap().is_compatible_with(other_elems.get(i).unwrap()) {
                        return false;
                    }
                }

                return true;
            }

            return false;
        }

        match &self {
            Self::Iterator(self_inner) => {
                match &other {
                    Self::Iterator(other_inner) | Self::Array(other_inner, _) => 
                        self_inner.is_compatible_with(&other_inner),

                    _ => false
                }
            }

            Self::Array(self_inner, self_size) => {
                match &other {
                    Self::Array(other_inner, other_size) => 
                        self_inner.is_compatible_with(&other_inner) && self_size == other_size,
                    
                    _ => false
                }

            }

            Self::Enum(self_name, _, _, _, _) => {
                match other {
                    Self::Enum(other_name, _, _, _, _) => self_name == other_name,
                    _ => false
                }
            }

            _ => false
        }
    }


    #[allow(unused)]
    pub fn get_size(&self) -> usize {
        match &self {
            Self::I32 | Self::U32 => 32,
            Self::I64 | Self::U64 => 64,
            Self::Bool => 8,
            other => unimplemented!("{:?} has not be implemented yet!", other)
        }
    }


    pub fn is_numeric(&self) -> bool {
        match self {
            Self::I32 | Self::I64 | Self::U32 | Self::U64 => true,
            _ => false
        }
    }


    pub fn add_behaviour(&mut self, behaviour_name: String, behaviour: Symbol) {
        match self {
            Self::Enum(_, _, _, items, _) => {
                items.insert(behaviour_name, behaviour);
            }
            _ => panic!()
        }
    }
}


/// Encodes a type, including the dependencies and linearity, of a value in Skopje. 
#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub basic_type: SimpleType,
    pub monadic: bool,
    pub dependencies: Vec<()>,
    pub linear: bool,
    pub generics: Vec<Type>
}


impl Type {
    pub fn new_str(basic_type: String, linear: bool, generics: Vec<Type>, context: &SymbolTable) -> Result<Self, Box<dyn Error>> {
        let basic_type = SimpleType::from_string(&basic_type, context)?;
        let monadic: bool = match basic_type {
            SimpleType::IOMonad => true,
            _ => false
        };

        Ok(Type { 
            dependencies: vec![], 
            basic_type,
            monadic,
            linear,
            generics
        })
    }


    pub fn new(basic_type: SimpleType, linear: bool, generics: Vec<Type>) -> Self {
        let monadic: bool = match basic_type {
            SimpleType::IOMonad => true,
            _ => false
        };

        Type {
            dependencies: vec![], 
            basic_type, 
            monadic, 
            linear, 
            generics
        }
    }


    pub fn from_basic(basic_type: SimpleType) -> Self {
        let monadic: bool = match basic_type {
            SimpleType::IOMonad => true,
            _ => false
        };

        Type {
            dependencies: vec![], 
            basic_type, 
            monadic, 
            linear: false, 
            generics: vec![]
        }
    }


    /// Converts Skopje types to their closest equivalents in C using the stdint.h library.
    pub fn as_ctype_str(&self) -> String {
        let basic_type_str = self.basic_type.as_ctype_str().to_owned();
        if self.monadic {
            return format!("{}<{}(*)()>", basic_type_str, self.generics.get(0).unwrap().as_ctype_str());
        }

        let generic_type_str = match self.generics.len() {
            0 => "".to_owned(),
            _ => format!(
                "<{}>", 
                self.generics
                    .iter()
                    .map(|g| g.as_ctype_str())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        };

        format!("{}{}", basic_type_str, generic_type_str)
    }


    pub fn is_numeric(&self) -> bool {
        self.basic_type.is_numeric()
    }


    pub fn is_compatible_with(&self, other: &Self) -> bool {
        self.basic_type.is_compatible_with(&other.basic_type)
    }


    pub fn add_behaviour(&mut self, behaviour_name: String, behaviour: Symbol) {
        self.basic_type.add_behaviour(behaviour_name, behaviour);
    }
}


#[cfg(test)]
mod tests {
    use super::*;


    #[test]
    fn test_type_compatibility() {
        assert!(SimpleType::I32.is_compatible_with(&SimpleType::I32));
        assert!(SimpleType::I64.is_compatible_with(&SimpleType::I32));
        assert!(SimpleType::U32.is_compatible_with(&SimpleType::U32));
        assert!(SimpleType::U64.is_compatible_with(&SimpleType::I32));
    }
}
