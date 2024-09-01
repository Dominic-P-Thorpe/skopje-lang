#![warn(missing_docs)]

use std::cell::RefCell;
use std::rc::{Rc, Weak};
use std::collections::HashMap;

use crate::parser::types::Type;


#[derive(Debug, Clone)]
pub enum SymbolType {
    // variable name, variable type
    Variable(String, Type),
    // enumeration name, enumeration variants
    EnumeraionType(String, Type),
    // function name, parameters, return type
    Function(String, Type)
}


impl ToString for SymbolType {
    fn to_string(&self) -> String {
        match self {
            Self::Variable(name, _) 
            | Self::Function(name, _) 
            | Self::EnumeraionType(name, _) => name.to_string()
        }
    }
}


impl SymbolType {
    pub fn get_type(&self) -> Type {
        match self {
            Self::Variable(_, t) 
            | Self::Function(_, t) 
            | Self::EnumeraionType(_, t) => t.clone()   
        }
    }
}


#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct Symbol {
    pub line: usize, // line on which the symbol was declared
    pub col: usize, // column on which the symbol was declared
    pub category: SymbolType // category of the symbol
}


impl Symbol {
    pub fn new(category: SymbolType, line: usize, col: usize) -> Self {
        Self {
            category,
            line,
            col
        }
    }


    pub fn get_type(&self) -> Type {
        self.category.get_type()
    }
}


#[derive(Debug)]
pub struct SymbolTable {
    table: HashMap<String, Symbol>,
    pub parent: Option<Weak<RefCell<SymbolTable>>>,
    pub children: Vec<Rc<RefCell<SymbolTable>>>,
}

impl SymbolTable {
    pub fn new(parent: Option<Weak<RefCell<SymbolTable>>>) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(SymbolTable {
            parent,
            table: HashMap::new(),
            children: vec![],
        }))
    }

    pub fn insert(&mut self, symbol: Symbol) {
        self.table.insert(symbol.category.to_string(), symbol);
    }

    pub fn get(&self, name: &String) -> Option<Symbol> {
        match self.table.get(name) {
            Some(symbol) => Some(symbol.clone()),
            None => match &self.parent {
                Some(p) => p.upgrade()?.borrow().get(name),
                None => None,
            },
        }
    }

    /// Adds a new child symbol table with the current symbol table as its parent.
    pub fn add_child(parent: &Rc<RefCell<Self>>) -> Rc<RefCell<Self>> {
        let child = SymbolTable::new(Some(Rc::downgrade(parent)));
        parent.borrow_mut().children.push(Rc::clone(&child));
        child
    }
}
