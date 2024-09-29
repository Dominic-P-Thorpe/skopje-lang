//! # Symbol Table Module
//!
//! This module provides the implementation of a symbol table that supports hierarchical 
//! relationships between symbol tables, allowing for efficient management and lookup of symbols in 
//! nested scopes.
//!
//! The symbol table is designed to store various types of symbols, such as variables, functions, 
//! and enumerations, each of which is represented by the `SymbolType` enum. Each symbol is 
//! associated with its type, the line and column where it was declared, and is stored in a `Symbol` 
//! struct.
//!
//! The `SymbolTable` struct allows for insertion and retrieval of symbols, supporting a 
//! hierarchical structure where each table can have a parent and multiple children. This makes it 
//! suitable for use in compilers and interpreters, where symbols need to be tracked across 
//! different scopes or blocks of code.
//!
//! ## Key Components:
//!
//! - **SymbolType**: An enum representing the different types of symbols that can be stored, such 
//! as variables, functions, and enumerations.
//! - **Symbol**: A struct representing a symbol, including its declaration position (line and 
//! column) and its category (type).
//! - **SymbolTable**: A struct representing a symbol table, which manages a collection of symbols 
//! and supports a parent-child relationship with other symbol tables.
//!
//! Example:
//!
//! ```rust
//! let root = SymbolTable::new(None); // Create the root symbol table with no parent
//! let child = SymbolTable::add_child(&root); // Add a child symbol table
//!
//! let symbol = Symbol::new(SymbolType::Variable("x".to_string(), Type::Int), 1, 1);
//! root.borrow_mut().insert(symbol); // Insert a symbol into the root table
//!
//! let retrieved_symbol = child.borrow().get(&"x".to_string()); // Retrieve the symbol from the child (checks the parent if not found)
//! assert!(retrieved_symbol.is_some()); // The symbol "x" should be found via the parent
//! ```
//!
//! This module is typically used in the context of a compiler's symbol resolution phase, but it can also be adapted to other use cases
//! where nested scopes and symbol management are required.
use std::cell::RefCell;
use std::rc::{Rc, Weak};
use std::collections::HashMap;

use crate::parser::types::{SimpleType, Type};


/// Represents different types of symbols that can be stored in the symbol table.
#[derive(Debug, Clone, PartialEq)]
pub enum SymbolType {
    /// Represents a variable with a name and a type.
    Variable(String, Type),
    /// Represents a struct with its name and type
    StructType(String, Type),
    /// Represents an enumeration with a name and its variants.
    EnumeraionType(String, Type, Vec<Symbol>),
    /// Represents a function with a name, parameters, and a return type.
    Function(String, Type)
}


impl ToString for SymbolType {
    /// Converts a `SymbolType` to a string, returning the name of the symbol.
    fn to_string(&self) -> String {
        match self {
            Self::Variable(name, _) 
            | Self::Function(name, _) 
            | Self::EnumeraionType(name, _, _)
            | Self::StructType(name, _) => name.to_string()
        }
    }
}


impl SymbolType {
    /// Returns the type associated with the `SymbolType`.
    pub fn get_type(&self) -> Type {
        match self {
            Self::Variable(_, t) 
            | Self::Function(_, t) 
            | Self::EnumeraionType(_, t, _)
            | Self::StructType(_, t) => t.clone()   
        }
    }
}


/// Represents a symbol in the symbol table with its location and type information.
#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
pub struct Symbol {
    /// The line number where the symbol was declared.
    pub line: usize,
    /// The column number where the symbol was declared.
    pub col: usize,
    /// If the symbol is mutable (always false unless a variable)
    pub mutable: bool,
    /// The category of the symbol, which defines what kind of symbol it is 
    /// (variable, function, etc.).
    pub category: SymbolType,
}


impl Symbol {
    /// Creates a new `Symbol` with the given category, line, and column.
    ///
    /// # Arguments
    ///
    /// * `category` - The type of symbol (variable, function, etc.).
    /// * `line` - The line number where the symbol is declared.
    /// * `col` - The column number where the symbol is declared.
    ///
    /// # Returns
    ///
    /// A new instance of `Symbol`.
    /// 
    /// # Example
    /// 
    /// ```
    /// Symbol::new(SymbolType::Variable(String::from("x"), Type::from_basic(SimpleType::I32)))
    /// ```
    pub fn new(category: SymbolType, mutable: bool, line: usize, col: usize) -> Self {
        Self {
            category,
            line,
            mutable,
            col
        }
    }


    /// Returns the type associated with this symbol.
    pub fn get_type(&self) -> Type {
        self.category.get_type()
    }
}


/// A struct representing a symbol table, which can store and retrieve symbols, and supports a 
/// hierarchical structure with parent and child symbol tables which represents the heirarchy of
/// scope within the program.
#[derive(Debug)]
pub struct SymbolTable {
    /// A hash map storing symbols by their names.
    table: HashMap<String, Symbol>,
    /// An optional weak reference to the parent symbol table.
    pub parent: Option<Weak<RefCell<SymbolTable>>>,
    /// A vector storing references to the child symbol tables.
    pub children: Vec<Rc<RefCell<SymbolTable>>>,
    /// If there is a "self", to what does it refer in this scope?
    pub self_ref: Option<Type>
}


impl PartialEq for SymbolTable {
    fn eq(&self, other: &Self) -> bool {
        self.table == other.table 
        && self.self_ref == other.self_ref 
        && self.children == other.children
    }
}


impl SymbolTable {
    /// Creates a new `SymbolTable` with an optional parent.
    ///
    /// # Arguments
    ///
    /// * `parent` - An optional weak reference to the parent symbol table.
    ///
    /// # Returns
    ///
    /// A reference-counted `Rc<RefCell<SymbolTable>>` pointing to the new symbol table.
    pub fn new(parent: Option<Weak<RefCell<SymbolTable>>>) -> Rc<RefCell<Self>> {
        // construct and insert the types of all the current stdlib functions
        let table = match &parent {
            Some(_) => HashMap::new(),
            None => {
                let mut functions: HashMap<String, Symbol> = HashMap::new();
                
                let print_type = Type::from_basic(SimpleType::IOMonad(
                    Box::new(Type::from_basic(SimpleType::Void)), None));

                let float2str_type = Type::from_basic(SimpleType::Function(
                    Box::new(Type::from_basic(SimpleType::Str)), 
                    vec![Type::from_basic(SimpleType::F64)]
                ));

                let int2str_type = Type::from_basic(SimpleType::Function(
                    Box::new(Type::from_basic(SimpleType::Str)), 
                    vec![Type::from_basic(SimpleType::I64)]
                ));

                let bool2str_type = Type::from_basic(SimpleType::Function(
                    Box::new(Type::from_basic(SimpleType::Str)), 
                    vec![Type::from_basic(SimpleType::Bool)]
                ));
        
                functions.insert("print".to_owned(), Symbol::new(SymbolType::Function("print".to_owned(), print_type), false, 0, 0));
                functions.insert("float2str".to_owned(), Symbol::new(SymbolType::Function("float2str".to_owned(), float2str_type), false, 0, 0));
                functions.insert("int2str".to_owned(), Symbol::new(SymbolType::Function("int2str".to_owned(), int2str_type), false, 0, 0));
                functions.insert("bool2str".to_owned(), Symbol::new(SymbolType::Function("bool2str".to_owned(), bool2str_type), false, 0, 0));


                functions
            }
        };

        Rc::new(RefCell::new(SymbolTable {
            table,
            parent: parent.clone(),
            children: vec![],
            self_ref: match parent {
                None => None,
                Some(p) => p.upgrade().unwrap().borrow().self_ref.clone()
            }
        }))
    }


    /// Inserts a new symbol into the symbol table.
    ///
    /// # Arguments
    ///
    /// * `symbol` - The `Symbol` to insert into the table.
    pub fn insert(&mut self, symbol: Symbol) {
        self.table.insert(symbol.category.to_string(), symbol);
    }


    /// Retrieves a symbol from the table by name.
    ///
    /// If the symbol is not found in the current table, the method will attempt to find it in the 
    /// parent table if there is one.
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the symbol to retrieve.
    ///
    /// # Returns
    ///
    /// An `Option` containing the `Symbol` if found, or `None` if not found.
    pub fn get(&self, name: &String) -> Option<Symbol> {
        match self.table.get(name) {
            Some(symbol) => Some(symbol.clone()),
            None => match &self.parent {
                Some(p) => p.upgrade()?.borrow().get(name),
                None => None,
            },
        }
    }

    // Adds a new child symbol table with the current symbol table as its parent.
    ///
    /// # Arguments
    ///
    /// * `parent` - A reference-counted pointer to the parent symbol table.
    ///
    /// # Returns
    ///
    /// A reference-counted `Rc<RefCell<SymbolTable>>` pointing to the new child symbol table.
    pub fn add_child(parent: &Rc<RefCell<Self>>) -> Rc<RefCell<Self>> {
        let child = SymbolTable::new(Some(Rc::downgrade(parent)));
        parent.borrow_mut().children.push(Rc::clone(&child));
        child
    }
}
