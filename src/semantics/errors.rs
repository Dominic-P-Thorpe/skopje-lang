use std::{fmt, error};

use super::typechecking::TypeField;


#[derive(Debug)]
pub struct TypeError {
    expected: TypeField,
    got: TypeField
}


impl TypeError {
    pub fn new(expected: TypeField, got: TypeField) -> Self {
         Self { expected, got }
    }
}


impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Expected expression of type {:?}, got {:?}", self.expected, self.got)
    }
}


impl error::Error for TypeError {}
