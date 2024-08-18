use std::{fmt, error};

use crate::parser::types::Type;


#[derive(Debug)]
pub struct TypeError {
    expected: Vec<Type>,
    got: Type
}


impl TypeError {
    pub fn new(expected: Vec<Type>, got: Type) -> Self {
         Self { expected, got }
    }
}


impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Expected expression of type {:?}, got {:?}", self.expected, self.got)
    }
}


impl error::Error for TypeError {}
