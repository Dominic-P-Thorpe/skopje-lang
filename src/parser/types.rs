use indexmap::IndexMap;
use std::{collections::HashMap, error::Error};

use crate::semantics::symbol_table::SymbolTable;

use super::errors::ParsingError;

#[derive(Debug, Clone, PartialEq)]
pub enum SimpleType {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Str,
    Void,
    Bool,
    Tuple(Vec<Type>),
    Array(Box<Type>, usize), // inner type, array size
    Iterator(Box<Type>), // inner type
    Struct(String, IndexMap<String, Type>, HashMap<String, Box<Type>>), // name and members
    Function(Box<Type>, Vec<Type>), // return type, vec of params
    /// - name of the enum
    /// - indexmap of names of variants to their members, which are composed of a member number 
    /// used to construct an instance of the enum of that member, and a hashmap of data members to 
    /// their types 
    /// - an option to denote which, if any, variant this enum type is of,
    /// - a hashmap of method names to their syntax trees, 
    /// - and a vector of traits the enum  inherits
    Enum(String, IndexMap<String, IndexMap<String, Type>>, Option<String>, HashMap<String, Box<Type>>, Vec<Type>),
    /// value's type and optional parameter
    IOMonad(Box<Type>, Option<Box<Type>>)
}


impl SimpleType {
    pub fn from_string(src: &str, symbol_table: &SymbolTable) -> Result<Self, Box<dyn Error>> {
        Ok(match src {
            "i8" => Self::I8,
            "i16" => Self::I16,
            "i32" => Self::I32,
            "i64" => Self::I64,
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" => Self::U64,
            "f32" => Self::F32,
            "f64" => Self::F64,
            "str" => Self::Str,
            "void" => Self::Void,
            "bool" => Self::Bool,
            "IO" => Self::IOMonad(Box::new(Type::from_basic(SimpleType::Void)), None),
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
            Self::I8 => String::from("int8_t"),
            Self::I16 => String::from("int16_t"),
            Self::I32 => String::from("int32_t"),
            Self::I64 => String::from("int64_t"),
            Self::U8 => String::from("uint8_t"),
            Self::U16 => String::from("uint16_t"),
            Self::U32 => String::from("uint32_t"),
            Self::U64 => String::from("uint64_t"),
            Self::F32 => String::from("float"),
            Self::F64 => String::from("double"),
            Self::Str => String::from("std::string"),
            Self::Bool => String::from("bool"),
            Self::IOMonad(rt, None) => format!("IO<{}>", rt.as_ctype_str()),
            Self::IOMonad(_, pt) => format!("{}", pt.as_ref().unwrap().as_ctype_str()),
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

            Self::Enum(name, _, _, _, _) | Self::Struct(name, _, _) => name.to_string()
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

            Self::IOMonad(self_rt, None) => {
                match other {
                    Self::IOMonad(other_rt, Some(param)) => {
                        self_rt.is_compatible_with(&other_rt) && self_rt.is_compatible_with(&*param)
                    }
                    _ => false
                }
            }

            _ => false
        }
    }


    #[allow(unused)]
    pub fn get_size(&self) -> usize {
        match &self {
            Self::I8  | Self::U8  => 8,
            Self::I16 | Self::U16 => 16,
            Self::I32 | Self::U32 | Self::F32 => 32,
            Self::I64 | Self::U64 | Self::F64 => 64,
            Self::Bool => 8,
            other => unimplemented!("{:?} has not be implemented yet!", other)
        }
    }


    pub fn is_numeric(&self) -> bool {
        match self {
            Self::I8 | Self::U8 
            | Self::I16 | Self::U16 
            | Self::I32 | Self::I64 
            | Self::U32 | Self::U64 
            | Self::F32 | Self::F64 => true,
            _ => false
        }
    }


    pub fn add_behaviour(&mut self, behaviour_name: String, behaviour: Type) {
        match self {
            Self::Enum(_, _, _, methods, _) | Self::Struct(_, _, methods) => {
                methods.insert(behaviour_name, Box::new(behaviour));
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
    pub linear: bool,
    pub generics: Vec<Type>
}


impl Type {
    pub fn new_str(basic_type: String, linear: bool, generics: Vec<Type>, context: &SymbolTable) -> Result<Self, Box<dyn Error>> {
        let basic_type = SimpleType::from_string(&basic_type, context)?;
        let monadic: bool = match basic_type {
            SimpleType::IOMonad(_, _) => true,
            _ => false
        };

        Ok(Type { 
            basic_type,
            monadic,
            linear,
            generics
        })
    }


    pub fn new(basic_type: SimpleType, linear: bool, generics: Vec<Type>) -> Self {
        let monadic: bool = match basic_type {
            SimpleType::IOMonad(_, _) => true,
            _ => false
        };

        Type {
            basic_type, 
            monadic, 
            linear, 
            generics
        }
    }


    pub fn from_basic(basic_type: SimpleType) -> Self {
        let monadic: bool = match basic_type {
            SimpleType::IOMonad(_, _) => true,
            _ => false
        };

        Type {
            basic_type, 
            monadic, 
            linear: false, 
            generics: vec![]
        }
    }


    /// Converts Skopje types to their closest equivalents in C using the stdint.h library.
    pub fn as_ctype_str(&self) -> String {
        let basic_type_str = self.basic_type.as_ctype_str().to_owned();

        // monads are a special case where we must handle the return types depending on how they
        // are being used
        if self.monadic {
            match &self.basic_type {
                // monad returns nothing and represents a function whcih returns nothing and has
                // no arguments
                SimpleType::Void => return format!("IO<std::function<{}()>>", basic_type_str),

                // a monad within a monad, requires flattening if it is a void monad
                SimpleType::IOMonad(rt, _) => return match rt.basic_type {
                    SimpleType::Void => format!("IO<std::function<void()>>"),
                    _ => return format!("IO<std::function<{0}({0})>>", self.basic_type.as_ctype_str())
                },

                // monad returns something of type t and represents a function f: t -> t
                _ => return format!("IO<std::function<{0}({0})>>", self.basic_type.as_ctype_str())
            }
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
        assert!(SimpleType::F32.is_compatible_with(&SimpleType::I64));
        assert!(SimpleType::F32.is_compatible_with(&SimpleType::U32));
        assert!(SimpleType::F64.is_compatible_with(&SimpleType::I64));
        assert!(SimpleType::F64.is_compatible_with(&SimpleType::U64));
    }
}
