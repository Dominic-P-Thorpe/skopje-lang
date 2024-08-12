use std::error::Error;

use super::errors::ParsingError;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimpleType {
    I32,
    U32,
    Str,
    Void,
    IOMonad
}


impl SimpleType {
    pub fn from_string(src: &str) -> Result<Self, Box<dyn Error>> {
        Ok(match src {
            "i32" => Self::I32,
            "u32" => Self::U32,
            "str" => Self::Str,
            "void" => Self::Void,
            "IO" => Self::IOMonad,
            name => return Err(Box::new(ParsingError::InvalidTypeName(name.to_owned())))
        })
    }


    /// Converts Skopje types to their closest equivalents in C using the stdint.h library.
    pub fn as_ctype_str(&self) -> &str {
        match self {
            Self::Void => "void",
            Self::I32 => "int32_t",
            Self::U32 => "uint32_t",
            Self::Str => "char*",
            Self::IOMonad => "IOMonad"
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
    pub fn new(basic_type: String, linear: bool, generics: Vec<Type>) -> Result<Self, Box<dyn Error>> {
        let basic_type = SimpleType::from_string(&basic_type)?;
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
}
