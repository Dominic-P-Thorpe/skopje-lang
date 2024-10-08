//! Translates an AST of Skopje code to C code which is then written to a file.
//! 
//! The struct [`Transpiler`] is used to translate the AST passed to it when it is instantiated into
//! C which is then written to the passed file. Reasonable effort has been made to ensure the 
//! resulting C code is readable.
//! 
//! In future, it will likely become necessary to package the resulting file of code along with a
//! makefile or other build system so that other files of source code can be included along with any
//! other libraries needed, including a garbage collector and/or arena allocator. Heirarchical
//! arena memory allocation is likely to be used.
//! 
//! # Examples
//! 
//! ```
//! fn main() {
//!     let scanner = Scanner::new("my_file.skj").unwrap();
//!     let mut parser = Parser::new(scanner.tokens, None);
//!     let ast = parser.parse().unwrap();
//!     let mut transpiler = Transpiler::new(ast, "out.c");
//! }
//! ``` 
use indexmap::IndexMap;
use rand::distributions::{Alphanumeric, DistString};
use std::cell::RefCell;
use std::collections::HashMap;
use std::error::Error;
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::rc::Rc;

use crate::parser::types::{Type, SimpleType};
use crate::semantics::symbol_table::SymbolTable;
use crate::semantics::typechecking::{fold_constexpr_index, get_array_inner_type, get_expr_type};
use crate::{Pattern, SyntaxNode, SyntaxTree};


/// The core of the transpiler module, containing data and methods needed to transpile from Skopje
/// to C code.
pub struct Transpiler {
    /// The target file to write the C code to
    file: File,
    // Extra functions which also need to be written to the file at the end of processing
    functions_source: Vec<String>,
    // Used to name auxilliary functions created by the compiler, not the programmer
    auxilliary_func_index: usize,
    // The symbol table for this scope in the program
    symbol_table: Rc<RefCell<SymbolTable>>,
    /// The AST to be translated into C
    ast: SyntaxTree
}


impl Transpiler {
    /// Creates a new instance of [`Transpiler`] which can be used to write the C translation of the
    /// given AST into the given directory.
    /// 
    /// The directory is created if it does not already exist, and is overwritten if it does.
    /// 
    /// # Example
    /// 
    /// ```
    /// let scanner = Scanner::new("my_file.skj").unwrap();
    /// let mut parser = Parser::new(scanner.tokens, None);
    /// let ast = parser.parse().unwrap();
    /// let mut transpiler = Transpiler::new(ast, "out.c");
    /// ```
    pub fn new(source: SyntaxTree, target: &str) -> Self {
        Transpiler { 
            file: OpenOptions::new().create(true).truncate(true).write(true).open(target).unwrap(), 
            functions_source: vec![],
            auxilliary_func_index: 0,
            ast: source,
            symbol_table: SymbolTable::new(None)
        }
    }


    /// Generates the name of the next compiler-generated auxilliary function and increments
    /// `self.auxilliary_func_index`.
    /// 
    /// The name returned is of the format `_F_<index>__<random_string>` where `index` is the 
    /// current auxilliary function index as a hexadecimal number padded to 8 digits, and 
    /// `random_string` is a randomly generated sequence of 16 alphanumeric or '_' characters
    /// appended to the end.
    /// 
    /// # Example
    /// 
    /// ```
    /// let transpiler: Transpiler = Transpiler::new(syntax_tree, "my_file.cpp");
    /// println!("{}", transpiler.get_next_auxilliary_func_name());
    /// ```
    #[allow(unused)]
    fn get_next_auxilliary_func_name(&mut self) -> String {
        let id_num: usize = self.auxilliary_func_index;
        self.auxilliary_func_index += 1;

        let mut rng = rand::thread_rng();
        let salt = Alphanumeric.sample_string(&mut rng, 16);
        format!("__F_{:#08X}__{}", id_num, salt)
    } 


    pub fn transpile_c(&mut self) -> Result<(), Box<dyn Error>> {
        self.file.write(b"#include \"c_libs/helper.h\"\n")?;

        if let SyntaxNode::Program(statements) = &self.ast.node.clone() {
            let statements_text: String = self.transpile_c_tree(&statements, 1)?;

            // write all the auxilliary functions to the source file
            for func in &self.functions_source {
                self.file.write(func.as_bytes())?;
                self.file.write(b"\n\n")?;
            }
            self.file.write(b"\n\n")?; // add in some extra line spacing
            
            self.file.write(statements_text.as_bytes())?;
            self.file.write(b"int main() {\n\tbind_if_monad(__special__main);\n\treturn 1;\n}")?;
            
            return Ok(());
        } 

        panic!("Could not transpile")
    }


    fn transpile_c_tree(&mut self, tree: &SyntaxTree, indent: usize) -> Result<String, Box<dyn Error>>{
        match &tree.node {
            SyntaxNode::StmtBlock(statements, symbol_table) => {
                let old_symbol_table = self.symbol_table.clone();
                self.symbol_table = symbol_table.clone();
                let mut statements_text = String::new();
                for statement in statements {
                    statements_text += &format!("\n{0}", "\t".repeat(indent));
                    statements_text += &self.transpile_c_tree(statement, 0)?;
                }

                self.symbol_table = old_symbol_table;
                Ok(statements_text)
            }

            SyntaxNode::Function(name, args, return_type, body) => {
                let args_string = args.iter()
                                      .map(|(p_id, p_type)| format!("{} {}", p_type.basic_type.as_ctype_str(), p_id))
                                      .collect::<Vec<String>>()
                                      .join(", ");
                let return_type_text = match return_type.basic_type {
                    SimpleType::IOMonad(_, _) => "auto".to_owned(),
                    _ => return_type.as_ctype_str()
                };

                let body_text = self.transpile_c_tree(body, indent + 1)?;
                
                // main function is a special case as it must have the return type of "int", so we
                // convert this function's name to a different name (__special__main())
                if name.as_str() == "main" {
                    return Ok(format!("\n{} __special__main() {{{} \n}}\n\n", return_type_text, body_text));
                }

                Ok(format!("\n{} {}({}) {{{} \n}}\n\n", return_type_text, name, args_string, body_text))
            }

            SyntaxNode::ReturnStmt(body) => {
                let body_text = self.transpile_typed_expr_c(&body, &Type::from_basic(SimpleType::Void))?;
                Ok("    ".repeat(indent) + "return " + &body_text + ";")
            }

            SyntaxNode::Program(_) => panic!("Got program when I should not have!"),

            SyntaxNode::FunctionCall(func_id, args) => {
                let func_type = self.symbol_table.borrow().get(func_id).unwrap().get_type();
                let func_arg_types = match func_type.basic_type {
                    SimpleType::Function(_, args) => args,
                    SimpleType::IOMonad(_, None) => vec![],
                    SimpleType::IOMonad(_, Some(param)) => vec![*param],
                    other => panic!("Expected function or IO monad, got {:?}", other)
                }; 

                let mut transpiled_args: Vec<String> = vec![];
                for i in 0..args.len() {
                    transpiled_args.push(self.transpile_typed_expr_c(args.get(i).unwrap(), &func_arg_types.get(i).unwrap()).unwrap())
                }

                if func_id == "print" {
                    return Ok(format!("{}std::cout << ({}) << std::endl;", "    ".repeat(indent), transpiled_args.first().unwrap()));
                } else if func_id == "readln" {
                    return Ok(format!("{}readln({});", "    ".repeat(indent), transpiled_args.first().unwrap()));
                }

                Ok(format!("{}{}({});", "    ".repeat(indent), func_id, transpiled_args.join(", ")))
            },

            SyntaxNode::SelectionStatement(cond, if_body, else_body) => {
                match &**else_body {
                    None => 
                        Ok(format!(
                            "{0}if ({1}) {{\n{2}\n{0}}}",
                            "    ".repeat(indent), 
                            self.transpile_typed_expr_c(cond, &Type::from_basic(SimpleType::Bool))?,
                            self.transpile_c_tree(if_body, indent + 1)?
                        )),

                    Some(else_body) => 
                        Ok(format!(
                            "{0}if ({1}) {{\n{2}\n{0}}} else {{\n{3}\n{0}}}", 
                            "    ".repeat(indent), 
                            self.transpile_typed_expr_c(cond, &Type::from_basic(SimpleType::Bool))?,
                            self.transpile_c_tree(if_body, indent + 1)?,
                            self.transpile_c_tree(&else_body, indent + 1)?
                        )) 
                }
            }

            SyntaxNode::ForStmt(iterator_name, iterator_type, iterator_expr, body) => {
                Ok(format!(
                    "{0}for ({1} {2} : {3}) {{\n{4}\n{0}}}\n",
                    "    ".repeat(indent),
                    iterator_type.as_ctype_str(),
                    iterator_name,
                    self.transpile_typed_expr_c(
                        iterator_expr, 
                        &Type::new(SimpleType::Iterator(Box::new(iterator_type.clone())), false, vec![])
                    )?,
                    self.transpile_c_tree(body, indent + 1)?
                ))
            }
            
            SyntaxNode::WhileStmt(cond, body) => {
                Ok(format!(
                    "{0}while ({1}) {{{2}{0}\n{0}\t}}\n", 
                    "    ".repeat(indent),
                    self.transpile_typed_expr_c(cond, &Type::from_basic(SimpleType::Bool))?,
                    self.transpile_c_tree(body, indent + 2)?
                ))
            }

            SyntaxNode::LetStmt(id, var_type, expr) => self.transpile_let_stmt(id, &var_type, &expr, indent),
            SyntaxNode::ReassignmentStmt(id, expr, var_type) => Ok(format!(
                "{}{} = {};",
                "    ".repeat(indent), 
                self.transpile_typed_expr_c(id, var_type)?,
                self.transpile_typed_expr_c(expr, var_type)?
            )),

            SyntaxNode::Enumeraion(name, variants, methods) => self.transpile_enum(name, variants, methods, indent),
            SyntaxNode::Struct(name, members, methods) => self.transpile_struct(name, members, methods, indent),
            SyntaxNode::MatchStmt(_, _, _) => self.transpile_match_stmt(tree, indent),
            SyntaxNode::ContinueStmt => Ok(format!("{}continue;", "\t".repeat(indent))),
            SyntaxNode::BreakStmt => Ok(format!("{}break;", "\t".repeat(indent))),
            other => panic!("{:?} is not a valid node!", other)
        }
    }


    fn transpile_let_stmt(
        &mut self, 
        id: &String, 
        var_type: &Type, 
        expr: &SyntaxTree, 
        indent: usize
    ) -> Result<String, Box<dyn Error>> {
        let is_const = match !self.symbol_table.borrow().get(id).unwrap().mutable {
            true => "const ",
            false => ""
        };

        let var_type = match var_type.clone().basic_type {
            SimpleType::IOMonad(rt, _) => Type::from_basic(SimpleType::IOMonad(rt, None)),
            _ => var_type.clone()
        };

        let var_type_str = match var_type.basic_type {
            SimpleType::IOMonad(_, _) => String::from("auto"),
            _ => var_type.as_ctype_str()
        };

        Ok(format!(
            "{}{}{} {} = {};",
            "    ".repeat(indent), 
            is_const,
            var_type_str,
            id, 
            self.transpile_typed_expr_c(expr, &var_type)?
        ))
    }


    fn transpile_struct(
        &mut self, 
        name: &str, 
        members: &IndexMap<String, Type>, 
        methods: &HashMap<String, SyntaxTree>, 
        indent: usize
    ) -> Result<String, Box<dyn Error>> {
        Ok(format!(
            "\nclass {1} {{\n{0}public:\n\t{2}\n\t{1}({3}) : {4} {{}}{5}\n{0}}};",
            "\t".repeat(indent),
            name,
            members.iter().map(|(k, v)| format!("{} {};\n", v.as_ctype_str(), k))
                   .collect::<Vec<String>>().join("\t"),
            members.iter().map(|(k, v)| format!("{} {}", v.as_ctype_str(), k))
                   .collect::<Vec<String>>().join(", "),
            members.iter().map(|(k, _)| format!("{0}({0})", k))
                   .collect::<Vec<String>>().join(", "),
            methods.iter().map(|(_, v)| self.transpile_c_tree(v, indent + 1).unwrap())
                   .collect::<Vec<String>>().join("")
        ))
    }


    fn transpile_match_stmt(&mut self, tree: &SyntaxTree, indent: usize) -> Result<String, Box<dyn Error>> {
        // TODO: adapt this to take non-enum expression types
        if let SyntaxNode::MatchStmt(match_expr, patterns, match_type) = &tree.node {
            assert!(patterns.len() > 0);
            let match_expr_str = self.transpile_typed_expr_c(&*match_expr, &match_type)?;
            return Ok(self.transpile_patterns(&patterns, &match_expr_str, match_type, indent + 1)?);
        }
        
        panic!("Expected match statement, got {:?}", tree)
    }


    fn transpile_patterns(&mut self, patterns: &Vec<(Pattern, SyntaxTree)>, match_expr_str: &str, match_expr_type: &Type, indent: usize) -> Result<String, Box<dyn Error>> {
        let mut patterns_strs: Vec<String> = vec![];
        for (pattern, body) in patterns {
            // get the first pattern in the list of patterns to match against
            match &pattern {
                Pattern::EnumPattern(enum_name, variant_name, inner_patterns) => {
                    let enum_name = match self.symbol_table.borrow().get(enum_name).unwrap().get_type().basic_type {
                        SimpleType::Enum(name, _, _, _, _) => name,
                        _ => panic!()
                    };
                    patterns_strs.push(self.transpile_enum_pattern(body, &enum_name, &variant_name, inner_patterns, match_expr_str, indent)?)
                } 

                Pattern::TuplePattern(_, patterns) => 
                    patterns_strs.push(self.transpile_tuple_pattern(patterns, match_expr_str, body, indent)?),
                    
                Pattern::ArrayPattern(_, patterns, end) =>
                    patterns_strs.push(self.transpile_array_pattern(patterns, match_expr_str, match_expr_type, body, end, indent)?),

                Pattern::IdentifierPattern(id) => 
                    patterns_strs.push(self.transpile_default_stmt(id, match_expr_str, match_expr_type, body, indent)?),

                Pattern::IntLiteralPattern(_, literal) => patterns_strs.push(format!(
                    "{0}if ({1} == {2}) {{{0}{3}\n{0}}}", 
                    "\t".repeat(indent), 
                    match_expr_str, literal, 
                    self.transpile_c_tree(body, indent + 1)?
                )),

                Pattern::FloatLiteralPattern(_, literal) => patterns_strs.push(format!(
                    "{0}if ({1} == {2}) {{{0}{3}\n{0}}}", 
                    "\t".repeat(indent), 
                    match_expr_str, literal, 
                    self.transpile_c_tree(body, indent + 1)?
                )),

                Pattern::BoolLiteralPattern(_, literal) => patterns_strs.push(format!(
                    "{0}if ({1} == {2}) {{{0}{3}\n{0}}}", 
                    "\t".repeat(indent), 
                    match_expr_str, literal, 
                    self.transpile_c_tree(body, indent + 1)?
                )),

                Pattern::StrLiteralPattern(_, literal) => patterns_strs.push(format!(
                    "{0}if ({1} == {2}) {{{0}{3}\n{0}}}", 
                    "\t".repeat(indent), 
                    match_expr_str, literal, 
                    self.transpile_c_tree(body, indent + 1)?
                )),

                Pattern::BetweenEqRangePattern(_, _, _)
                | Pattern::GreaterThanEqRangePattern(_, _)
                | Pattern::LessThanEqRangePattern(_, _) => patterns_strs.push(format!(
                    "{0}if ({1}) {{{0}{2}\n{0}}}",
                    "\t".repeat(indent),
                    self.transpile_conditional_patterns(&vec![pattern.clone()], match_expr_str),
                    self.transpile_c_tree(body, indent + 1)?
                )),
            }
        }

        // join the pattern branches together
        Ok(patterns_strs.join("\n"))
    }


    fn transpile_default_stmt(
        &mut self, 
        id: &str, 
        match_expr_str: &str, 
        match_expr_type: &Type, 
        body: &SyntaxTree, 
        indent: usize
    ) -> Result<String, Box<dyn Error>> {
        match match_expr_type.basic_type {
            SimpleType::Enum(_, _, _, _, _) =>
                Ok(format!(
                    "{0}else {{\n\t{0}auto {1} = {2}.getValue();\n{3}\n\t{0}\n{0}}}", 
                    "    ".repeat(indent),
                    id, match_expr_str,
                    self.transpile_c_tree(body, indent + 1)?,
                )),
            _ => 
            Ok(format!(
                "{0}else {{\n\t{0}auto {1} = {2};\n{3}\n\t{0}\n{0}}}", 
                "    ".repeat(indent),
                id, match_expr_str,
                self.transpile_c_tree(body, indent + 1)?,
            ))
        }
    }


    fn transpile_array_pattern(
        &mut self, 
        patterns: &Vec<Pattern>,
        match_expr_str: &str, 
        match_expr_type: &Type, 
        body: &SyntaxTree, 
        end: &Box<Option<Pattern>>, 
        indent: usize
    ) -> Result<String, Box<dyn Error>> {
        let pattern_variables_strs: String = self.get_array_pattern_variables(patterns, match_expr_str, match_expr_type, end, indent);
        let conditions_strs: String = self.transpile_conditional_patterns(patterns, match_expr_str);
        
        Ok(format!(
            "{1}\n{0}\tif ({3}) {{{0}{2}\n{0}\t}}", 
            "\t".repeat(indent - 1), 
            pattern_variables_strs, 
            self.transpile_c_tree(body, indent + 1)?,
            conditions_strs
        ))
    }


    fn get_array_pattern_variables(
        &mut self, 
        patterns: &Vec<Pattern>, 
        match_expr_str: &str, 
        match_expr_type: &Type, 
        end: &Box<Option<Pattern>>, 
        indent: usize
    ) -> String {
        let mut pattern_variables_strs: Vec<String> = vec![];
        for i in 0..patterns.len() {
            let pattern= patterns.get(i).unwrap();
            match pattern {
                Pattern::BoolLiteralPattern(id, _)
                | Pattern::IntLiteralPattern(id, _)
                | Pattern::StrLiteralPattern(id, _)
                | Pattern::IdentifierPattern(id) => 
                    pattern_variables_strs.push(format!("{}auto {} = {}[{}];", "\t".repeat(indent - 1), id, match_expr_str, i)),
                Pattern::TuplePattern(_, sub_patterns) => {
                    let new_match_expr_str = format!("std::get<{}>({})", i, match_expr_str);
                    pattern_variables_strs.push(self.get_tuple_pattern_variables(sub_patterns, &new_match_expr_str, indent))
                }
                _ => ()
            }
        }

        match &**end {
            None => (),
            Some(pattern) => match pattern {
                Pattern::IdentifierPattern(id) => pattern_variables_strs.push(format!(
                    "{}auto {} = get_last_elements<{}, {}>({});",
                    "\t".repeat(indent - 1),
                    id,
                    match_expr_type.as_ctype_str(),
                    patterns.len() + 1,
                    match_expr_str
                )),
                _ => panic!()
            }
        }

        pattern_variables_strs.join("\n\t")
    }


    fn transpile_tuple_pattern(&mut self, patterns: &Vec<Pattern>, match_expr_str: &str, body: &SyntaxTree, indent: usize) -> Result<String, Box<dyn Error>> {
        let pattern_variables_strs: String = self.get_tuple_pattern_variables(patterns, match_expr_str, indent);
        let conditions_strs: String = self.transpile_conditional_patterns(patterns, match_expr_str);

        Ok(format!(
            "{1}\n{0}\tif ({3}) {{{0}{2}\n{0}\t}}", 
            "\t".repeat(indent - 1), 
            pattern_variables_strs, 
            self.transpile_c_tree(body, indent + 1)?,
            conditions_strs
        ))
    }


    fn get_tuple_pattern_variables(&self, patterns: &Vec<Pattern>, match_expr_str: &str, indent: usize) -> String {
        let mut pattern_variables_strs: Vec<String> = vec![];
        for i in 0..patterns.len() {
            let pattern= patterns.get(i).unwrap();
            match pattern {
                Pattern::BoolLiteralPattern(id, _)
                | Pattern::IntLiteralPattern(id, _)
                | Pattern::StrLiteralPattern(id, _)
                | Pattern::IdentifierPattern(id) => 
                    pattern_variables_strs.push(format!("{}auto {} = std::get<{}>({});", "\t".repeat(indent - 1), id, i, match_expr_str)),
                Pattern::TuplePattern(_, sub_patterns) => {
                    let new_match_expr_str = format!("std::get<{}>({})", i, match_expr_str);
                    pattern_variables_strs.push(self.get_tuple_pattern_variables(sub_patterns, &new_match_expr_str, indent))
                }
                _ => ()
            }
        }

        pattern_variables_strs.join("\n\t")
    }


    fn transpile_enum_pattern(
        &mut self, 
        body: &SyntaxTree, 
        enum_name: &String, 
        variant_name: &str, 
        inner_patterns: &Vec<Pattern>, 
        match_expr_str: &str, 
        indent: usize
    ) -> Result<String, Box<dyn Error>> {
        let mut patterns_strs: Vec<String> = vec![];
        let enum_type: Type = match &body.node {
            SyntaxNode::StmtBlock(_, symbol_table) => 
                symbol_table.borrow().get(enum_name).unwrap().get_type(),
            _ => panic!()
        };

        patterns_strs.push(format!(
            "
{0}if ({7} == {1}::{2}) {{
{0}    auto iu = {4}.{5};
{6}      
{0}    if ({8}) {{
            {0}{3}
{0}    }}
{0} }}",
            "    ".repeat(indent),
            enum_name,
            variant_name,
            // transpile the body of the pattern branch
            self.transpile_c_tree(body, indent + 2)?,
            match match_expr_str {
                "this" => "this->getValue()",
                _ => "this.getValue()"
            },
            variant_name.to_lowercase(),
            self.transpile_enum_data_params(inner_patterns, &enum_type, variant_name, indent + 1),
            match match_expr_str {
                "this" => "this->getTag()",
                _ => "this"
            },
            self.transpile_conditional_patterns(inner_patterns, match_expr_str)
        ));

        Ok(patterns_strs.join("\n"))
    }


    fn transpile_conditional_patterns(&self, sub_patterns: &Vec<Pattern>, match_expr_str: &str) -> String {
        let mut sub_pattern_strs: Vec<String> = vec![];
        for sub_pattern in sub_patterns {
            match sub_pattern {
                Pattern::IntLiteralPattern(id, literal) => sub_pattern_strs.push(format!("{} == {:?}", id, literal)),
                Pattern::FloatLiteralPattern(id, literal) => sub_pattern_strs.push(format!("{} == {:?}", id, literal)),
                Pattern::StrLiteralPattern(id, literal) => sub_pattern_strs.push(format!("{} == {:?}", id, literal)),
                Pattern::BoolLiteralPattern(id, literal) => sub_pattern_strs.push(format!("{} == {:?}", id, literal)),
                Pattern::TuplePattern(_, sub_sub_patterns) => sub_pattern_strs.push(self.transpile_conditional_patterns(sub_sub_patterns, match_expr_str)),
                Pattern::BetweenEqRangePattern(_, start, end) => sub_pattern_strs.push(format!("{1} >= {0} && {0} <= {2}", match_expr_str, start, end)),
                Pattern::LessThanEqRangePattern(_, start) => sub_pattern_strs.push(format!("{} <= {}", match_expr_str, start)),
                Pattern::GreaterThanEqRangePattern(_, start) => sub_pattern_strs.push(format!("{} >= {}", match_expr_str, start)), 
                Pattern::IdentifierPattern(_) => (),
                Pattern::EnumPattern(_, _, _)  
                | Pattern::ArrayPattern(_, _, _) => unimplemented!(),
            } 
        }

        if sub_pattern_strs.len() == 0 {
            return String::from("1");
        }

        sub_pattern_strs.join(" && ")
    }


    /// Converts the data parameters into variable assignments which go at the top of the enum
    /// variant's case block and can then be used in the rest of the block to access the fields
    /// of the parameter
    fn transpile_enum_data_params(&mut self, inner_patterns: &Vec<Pattern>, enum_type: &Type, variant_name: &str, indent: usize) -> String {
        let enum_variants = match &enum_type.basic_type {
            SimpleType::Enum(_, variants, _, _, _) => variants.get(variant_name).unwrap(),
            other => panic!("Expected enum, got {:?}", other)
        };

        assert_eq!(enum_variants.len(), inner_patterns.len());

        let mut params_str: String = String::new();
        for i in 0..enum_variants.len() {
            let pattern_param_name = match &inner_patterns.get(i).unwrap() {
                Pattern::IdentifierPattern(id)
                | Pattern::BoolLiteralPattern(id, _)
                | Pattern::IntLiteralPattern(id, _)
                | Pattern::StrLiteralPattern(id, _)
                | Pattern::TuplePattern(id, _) => id,
                _ => panic!()
            };

            let enum_param_name = enum_variants.get_index(i).unwrap().0;
            params_str += &format!("{0}auto {1} = iu.{2};\n", "\t".repeat(indent), pattern_param_name, enum_param_name);

            match inner_patterns.get(i).unwrap() {
                Pattern::TuplePattern(_, patterns) => {
                    params_str += "\t";
                    params_str += &self.get_tuple_pattern_variables(patterns, &pattern_param_name, indent);
                }
                _ => ()
            }
        }

        params_str
    }


    fn transpile_typed_expr_c(&mut self, tree: &SyntaxTree, target: &Type) -> Result<String, Box<dyn Error>> {
        match &tree.node {
            SyntaxNode::TernaryExpression(cond, if_true, if_false) =>
                Ok(self.transpile_typed_expr_c(cond, &Type::from_basic(SimpleType::Bool))? + " ? " 
                    + &self.transpile_typed_expr_c(if_true, target)? + " : " 
                    + &self.transpile_typed_expr_c(if_false, target)?),
            SyntaxNode::BinaryOperation(op, l, r) => {
                // special handling for primitive operations not found in C++ natively
                match op.as_str() {
                    "::" => Ok(format!("concatenate({}, {})", self.transpile_typed_expr_c(l, target)?, self.transpile_typed_expr_c(r, target)?)),
                    "->" => {
                        let left_side = match get_expr_type(l, &self.symbol_table.clone().borrow())?.basic_type {
                            SimpleType::IOMonad(_, _) => self.transpile_typed_expr_c(l, target)?,
                            _ => format!("{}({})", target.basic_type.as_ctype_str(), self.transpile_typed_expr_c(l, target)?)
                        };

                        match get_expr_type(r, &self.symbol_table.clone().borrow())?.basic_type {
                            SimpleType::IOMonad(inner, _) => match inner.basic_type {
                                SimpleType::Void => Ok(format!(
                                    "{}.arrow({})", 
                                    left_side, 
                                    self.transpile_typed_expr_c(r, target)?
                                )),
    
                                _ => Ok(format!(
                                    "{0}.arrow<std::function<{1}({1})>>({2})", 
                                    left_side, 
                                    get_expr_type(r, &self.symbol_table.clone().borrow())?.basic_type.as_ctype_str(), 
                                    self.transpile_typed_expr_c(r, target)?
                                ))
                            }
                            other => Ok(other.as_ctype_str())
                        }
                    }
                    ".." => {
                        let start = fold_constexpr_index(&l);
                        let end = fold_constexpr_index(&r);
                        Ok(format!("array_range<{}, {}>({}, {})", get_array_inner_type(&target).as_ctype_str(), usize::abs_diff(start, end), start, end))
                    }
                    "." => {
                        let operator = match l.node {
                            SyntaxNode::SelfIdentifier => "->",
                            _ => "."
                        };

                        Ok(format!("{}{}{}", self.transpile_typed_expr_c(l, target)?, operator, self.transpile_typed_expr_c(r, target)?))
                    }
                    ">>" => Ok(format!("arith_right({}, {})", self.transpile_typed_expr_c(l, &Type::from_basic(SimpleType::I64))?, self.transpile_typed_expr_c(l, &Type::from_basic(SimpleType::U64))?)),
                    ">>>" => Ok(format!("logical_right({}, {})", self.transpile_typed_expr_c(l, &Type::from_basic(SimpleType::U64))?, self.transpile_typed_expr_c(l, &Type::from_basic(SimpleType::U64))?)),
                    _ => Ok(format!("{} {} {}", self.transpile_typed_expr_c(l, target)?, op, self.transpile_typed_expr_c(r, target)?)) 
                }
            }
            SyntaxNode::RightAssocUnaryOperation(op, r) => 
                Ok(op.to_owned() + " " + &self.transpile_typed_expr_c(r, target)?),
            SyntaxNode::LeftAssocUnaryOperation(op, l) => 
                Ok(self.transpile_typed_expr_c(l, target)? + " " + op),
            SyntaxNode::TupleIndexingOperation(index, l) => 
                Ok(format!("std::get<{}>({})", self.transpile_typed_expr_c(index, target)?, self.transpile_typed_expr_c(l, target)?)),
            SyntaxNode::ArrayIndexingOperation(index, l) => 
                Ok(format!("{}[{}]", self.transpile_typed_expr_c(l, target)?, self.transpile_typed_expr_c(index, target)?)),
            SyntaxNode::ParenExpr(expr) => 
                Ok("(".to_owned() + &self.transpile_typed_expr_c(expr, target)? + ")"),
            SyntaxNode::StringLiteral(s) => Ok(format!("\"{}\"", s)),
            SyntaxNode::IntLiteral(n) => Ok(n.to_string()),
            SyntaxNode::BoolLiteral(true) => Ok("true".to_owned()),
            SyntaxNode::BoolLiteral(false) => Ok("false".to_owned()),
            SyntaxNode::Identifier(id) => Ok(id.to_owned()),

            SyntaxNode::FloatLiteral(f) => if f.fract() == 0.0 {
                Ok(format!("{}.0", f.to_string()))
            } else {
                Ok(format!("{}", f.to_string()))
            } 

            SyntaxNode::SubarrayOperation(root, root_type, start, end) => {
                match &root_type.basic_type {
                    SimpleType::Array(_, len) => 
                        Ok(format!("subarray<{0}, {1}, {2}, {3}>({4}, {2}, {3})", get_array_inner_type(&target).as_ctype_str(), len, start, end, self.transpile_typed_expr_c(root, target)?)),
                    other => panic!("Expected array, got {:?}", other)
                }
            }

            SyntaxNode::FunctionCall(func_id, args) => {
                let func_type = self.symbol_table.borrow().get(func_id).unwrap().get_type();
                let func_arg_types = match func_type.basic_type {
                    SimpleType::Function(_, args) => args,
                    SimpleType::IOMonad(_, _) => vec![],
                    other => panic!("Expected function or IO monad, got {:?}", other)
                }; 

                let mut transpiled_args: Vec<String> = vec![];
                for i in 0..args.len() {
                    transpiled_args.push(self.transpile_typed_expr_c(args.get(i).unwrap(), &func_arg_types.get(i).unwrap()).unwrap())
                }
                
                if func_id == &String::from("print") {
                    return Ok(format!("printf({})", transpiled_args.first().unwrap()));
                }

                Ok(format!("{}({})", func_id, &transpiled_args.join(", ")))
            },

            SyntaxNode::TupleLiteral(expressions) => {
                Ok(format!(
                    "std::make_tuple({})",
                    expressions.iter()
                               .map(|e| self.transpile_typed_expr_c(e, target).unwrap())
                               .collect::<Vec<String>>()
                               .join(", ")
                ))
            }

            SyntaxNode::ArrayLiteral(elems, _) => {
                Ok(format!(
                    "make_array<{}, {}>({})",
                    get_array_inner_type(&target).as_ctype_str(),
                    elems.len(),
                    elems.iter()
                         .map(|e| self.transpile_typed_expr_c(e, &get_array_inner_type(&target)).unwrap())
                         .collect::<Vec<String>>()
                         .join(", ")
                ))
            }

            SyntaxNode::EnumInstantiation(enum_type, variant, args) => match &enum_type.basic_type {
                SimpleType::Enum(name, variants, _, _, _) => {
                    let variant_data: &IndexMap<String, Type> = variants.get(variant).unwrap();
                    let args_str = args.iter()
                                       .map(|(_, v)| self.transpile_typed_expr_c(&v, &Type::from_basic(SimpleType::I32)).unwrap())
                                       .collect::<Vec<String>>().join(", ");
                    
                    if variant_data.len() == 0 {
                        Ok(format!("{}({})", name, variants.get_index_of(variant).unwrap()))
                    } else {
                        Ok(format!("{}({}, {})", name, variants.get_index_of(variant).unwrap(), args_str))
                    }
                }
                _ => panic!()
            }

            SyntaxNode::TypeCast(new_type, old_type, rhs) => 
                Ok(format!("({}){}", new_type.as_ctype_str(), self.transpile_typed_expr_c(rhs, old_type)?)),

            SyntaxNode::SelfIdentifier => Ok(format!("this")),

            SyntaxNode::StructInstantiation(name, members) => Ok(format!(
                "{}({})",
                name,
                members.iter().map(|(_, v)| self.transpile_typed_expr_c(v, &Type::from_basic(SimpleType::Void)).unwrap())
                       .collect::<Vec<String>>().join(", ")
            )),

            SyntaxNode::ConcatStr(l, r) => Ok(format!(
                "{} + {}", 
                self.transpile_typed_expr_c(l, &Type::from_basic(SimpleType::Str))?,
                self.transpile_typed_expr_c(r, &Type::from_basic(SimpleType::Str))?
            )),

            SyntaxNode::MonadicExpr(body, Some((param_id, param_type)), rt) => {
                let captured_vars = self.get_captured_lambda_variables(body, &vec![param_id.to_string()]);
                let monad_body = self.transpile_c_tree(&body, 1)?;
                let monad_lambda = format!("[{}]({} {}) {{\n{}\n}}", captured_vars.join(", "), param_type.as_ctype_str(), param_id, monad_body);
                Ok(format!("IO<std::function<{0}({0})>>({1})", rt.as_ctype_str(), monad_lambda))
            }

            SyntaxNode::MonadicExpr(body, None, rt) => {
                let captured_vars = self.get_captured_lambda_variables(body, &vec![]);
                let monad_body = self.transpile_c_tree(&body, 1)?;
                let monad_lambda = format!("[{}]() {{\n{}\n}}", captured_vars.join(", "), monad_body);
                Ok(format!("IO<std::function<{}()>>({})", rt.as_ctype_str(), monad_lambda))
            }

            other => panic!("{:?} is not a valid expression node!", other)
        }
    }


    fn get_captured_lambda_variables(&self, tree: &SyntaxTree, excluded: &Vec<String>) -> Vec<String> {
        match &tree.node {
            SyntaxNode::Identifier(id) => if !excluded.contains(&id) {
                vec![id.to_string()]
            } else { vec![] },

            SyntaxNode::ReturnStmt(body)
            | SyntaxNode::LetStmt(_, _, body)
            | SyntaxNode::ReassignmentStmt(_, body, _)
            | SyntaxNode::LeftAssocUnaryOperation(_, body)
            | SyntaxNode::RightAssocUnaryOperation(_, body) => self.get_captured_lambda_variables(&*body, excluded),

            SyntaxNode::BinaryOperation(op, l, r) => match op.as_str() {
                "." => self.get_captured_lambda_variables(&*l, excluded),
                _ => vec![
                    self.get_captured_lambda_variables(&*l, excluded),
                    self.get_captured_lambda_variables(&*r, excluded)
                ].concat()
            },

            SyntaxNode::ConcatStr(l, r) => vec![
                self.get_captured_lambda_variables(&*l, excluded),
                self.get_captured_lambda_variables(&*r, excluded)
            ].concat(),

            SyntaxNode::TernaryExpression(expr, l, r) => vec![
                self.get_captured_lambda_variables(&*expr, excluded),
                self.get_captured_lambda_variables(&*l, excluded),
                self.get_captured_lambda_variables(&*r, excluded)
            ].concat(),

            SyntaxNode::StmtBlock(body, _) => self.get_captured_lambda_variables_from_vec(&body, excluded),
            SyntaxNode::WhileStmt(expr, body)
            | SyntaxNode::ForStmt(_, _, expr, body) => vec![
                self.get_captured_lambda_variables(&*expr, excluded),
                self.get_captured_lambda_variables(&*body, excluded)
            ].concat(),

            SyntaxNode::FunctionCall(_, params) => self.get_captured_lambda_variables_from_vec(params, excluded),
            SyntaxNode::SelectionStatement(body, expr, else_block) => {
                match &**else_block {
                    None => vec![
                        self.get_captured_lambda_variables(&*expr, excluded),
                        self.get_captured_lambda_variables(&*body, excluded)
                    ].concat(),

                    Some(e) => vec![
                        self.get_captured_lambda_variables(&*expr, excluded),
                        self.get_captured_lambda_variables(&*body, excluded),
                        self.get_captured_lambda_variables(&e, excluded)
                    ].concat()
                }
            }

            _ => vec![]
        }
    }


    fn get_captured_lambda_variables_from_vec(&self, body: &Vec<SyntaxTree>, excluded: &Vec<String>) -> Vec<String> {
        body.into_iter()
            .map(|s| self.get_captured_lambda_variables(s, excluded))
            .collect::<Vec<Vec<String>>>()
            .concat()
    }


    fn transpile_enum(
        &mut self, 
        name: &String, // name of the enum to transpile
        variants: &Vec<SyntaxTree>, // variants the enum may take,
        methods: &HashMap<String, SyntaxTree>,
        indent: usize // current output file indentation level
    ) -> Result<String, Box<dyn Error>> {
        let string = format!("
class {0} {{
public:
    enum Tag {{
        {1}
    }};

    union InternalUnion {{
        {2}

        InternalUnion() {{}}
        ~InternalUnion() {{}}
    }};
    
    template <typename... Args>
    {0}(int variant, Args... args) {{
        this->tag = static_cast<Tag>(variant);
        switch(this->tag) {{{3}\t\t}};
    }}

    InternalUnion getValue() {{
        return this->value;
    }}

    Tag getTag() {{ 
        return this->tag; 
    }}

    {4}


private:
    InternalUnion value;
    Tag tag;
}};\n\n", 
            name, // name of the enumeration
            // names of the variants as a comma-and-newline-separated list indented appropriately to 
            // be members of the Tag enum
            variants.iter().map(
                |v| match &v.node {
                    SyntaxNode::EnumVariant(name, _) => capitalize(name),
                    _ => panic!()
                }
            ).collect::<Vec<String>>().join(&format!(",\n\t\t{}", "    ".repeat(indent))),

            // the members of the internal union, formatted as "struct <CAPITALIZED_NAME> {} 
            // <LOWERCASE_NAME>;"
            variants.iter()
                    .map(|v| self.transpile_variant_to_struct(v))
                    .collect::<Vec<String>>()
                    .join(&format!("\n\t\t{}", "    ".repeat(indent))),

            // the switch statement for the constructor which contains a case for each variant in
            // the enumeration to ensure proper instantiation
            variants.iter().map(
                |v| match &v.node {
                    SyntaxNode::EnumVariant(name, data_params) => format!("
            case {0}:
                this->value.{1} = create_struct<InternalUnion::{0}, {2}>(args...);
                break;
", 
                        capitalize(name), 
                        name.to_lowercase(),
                        data_params.len()
                    ),
                    _ => panic!()
                }
            ).collect::<Vec<String>>().join(&format!("\t\t{}", "    ".repeat(indent))),

            methods.iter().map(|(_, v)| self.transpile_c_tree(v, indent + 1).unwrap())
                   .collect::<Vec<String>>().join("")
        );
        Ok(string)
    }


    fn transpile_variant_to_struct(&self, variant: &SyntaxTree) -> String {
        match &variant.node {
            SyntaxNode::EnumVariant(name, args) =>
                if args.len() == 0 {
                    format!("struct {} {{}} {};", capitalize(&name), name.to_lowercase())
                } else {
                    format!(
                        "struct {} {{\n{}\n\t\t}} {};", 
                        capitalize(&name),
                        args.iter().map(|(k, v)| format!("\t\t\t{} {};", v.as_ctype_str(), k)).collect::<Vec<String>>().join(";\n"),
                        name.to_lowercase()
                    )
                }
            _ => panic!()
        }
    }
}


/// Taken from: https://nick.groenen.me/notes/capitalize-a-string-in-rust/
pub fn capitalize(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
    }
}


#[cfg(test)]
mod test {
    use std::process::Command;

    use crate::parser::parsing::Parser;
    use crate::parser::lexing::Scanner;
    use super::Transpiler;


    #[test]
    fn test_for_loop() {
        let scanner = Scanner::new("tests/should_pass/test_for_loop.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_basic_enum_match() {
        let scanner = Scanner::from_str("
            enum MyEnum { VariantA, VariantB, VariantC }

            fn main() -> i32 {
                let my_enum: MyEnum = MyEnum::VariantA;
                match my_enum {
                    MyEnum::VariantA => { return 1; },
                    MyEnum::VariantB => { return 2; },
                    MyEnum::VariantC => { return 3; }
                }

                return 0;
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_match_self() {
        let scanner = Scanner::new("tests/should_pass/test_match_self.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_basic_enum_data_match() {
        let scanner = Scanner::from_str("
            enum MyEnum { VariantA(a: i32, b: u32), VariantB(a: i32), VariantC }

            fn main() -> i32 {
                let my_enum: MyEnum = MyEnum::VariantA(a: 1, b: 2);
                match my_enum {
                    MyEnum::VariantA(x, y) => { return x + y + 1; },
                    MyEnum::VariantB(a) => { return a; },
                    MyEnum::VariantC => { return 3; }
                }

                return 0;
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_enum_with_enum_as_data_param() {
        let scanner = Scanner::new("tests/should_pass/test_enum_with_enum_as_data_param.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_match_enum_with_specific_data_param() {
        let scanner = Scanner::from_str("
            enum MyEnum { VariantA(a: i32, b: u32), VariantB(a: i32), VariantC }

            fn main() -> i32 {
                let my_enum: MyEnum = MyEnum::VariantA(a: 1, b: 2);
                match my_enum {
                    MyEnum::VariantA(x, 10) => { return x + 1; },
                    MyEnum::VariantA(x, y) => {return x + y + 1; },
                    MyEnum::VariantB(a) => { return a; },
                    MyEnum::VariantC => { return 3; }
                }

                return 0;
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    #[ignore]
    fn test_enum_match_with_multiple_patterns() {
        todo!()
    }


    #[test]
    fn test_nested_tuple_pattern() {
        let scanner = Scanner::from_str("
            fn main() -> i32 {
            let e: (i32, bool, (i32, i32)) = (1, true, (2, 3));
            match e {
                (1, true, (y, 5)) => { return 1; },
                (a, b, c) => { return 2; }
            }
            return 0;
        }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_match_tuple_in_enum_pattern() {
        let scanner = Scanner::from_str("
            enum MyEnum { VariantA, VariantB(x: (i32, i32)) }


            fn main() -> i32 {
                let e: MyEnum = MyEnum::VariantB(x: (1, 2));
                match e {
                    MyEnum::VariantA => {
                        return 0;
                    },

                    MyEnum::VariantB((1, 2)) => {
                        return 1;
                    },

                    MyEnum::VariantB(x) => {
                        return 2;
                    }
                }
                return 0;
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_struct_with_methods() {
        let scanner = Scanner::new("tests/should_pass/test_struct_with_methods.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_string_io() {        
        let scanner = Scanner::from_str("
            fn print_hello_world() -> IO<void> {
                return do {
                    print(\"Hello world!\");
                };
            }
            
            
            fn main() -> IO<void> {
                return print_hello_world();
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_composite_string_io() {
        let scanner = Scanner::new("tests/should_pass/test_composite_string_io.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_composite_int_io() {
        let scanner = Scanner::from_str("
            fn square() -> IO<i32> {
                return do(x: i32) {
                    return x * x;
                };
            }


            fn main() -> i32 {
                let m: IO<i32> = 10 -> square();
                return 1;
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_do_block_literal_composition() {
        let scanner = Scanner::from_str("
            fn main() -> IO<void> {
                return do {
                    print(\"Hey there\");
                } -> do {
                    print(\"Hello world!\");
                };
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    fn test_externally_bound_variables() {
        let scanner = Scanner::new("tests/should_pass/test_externally_bound_variables.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
    }


    #[test]
    fn test_runge_kutta() {
        let scanner = Scanner::new("tests/should_pass/test_runge_kutta.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }


    #[test]
    #[should_panic]
    fn test_invalid_composition_types() {
        let scanner = Scanner::from_str("
            fn main() -> IO<void> {
                return do {
                    print(\"Hey there\");
                } -> do {
                    return 1.0;
                };
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
        Command::new("cmd").args(["g++ test_out.cpp -std=c++20"]).output().unwrap();
    }
    

    #[test]
    #[should_panic]
    #[ignore]
    fn test_non_total_enum_match() {
        todo!()
    }


    #[test]
    #[should_panic]
    fn test_incorrect_num_enum_init_data_params() {
        let scanner = Scanner::from_str("
            enum MyEnum = VariantA(a: i32, b: u32) | VariantB(a: i32) | VariantC;

            fn main() -> i32 {
                let my_enum: MyEnum = MyEnum::VariantA;
                match my_enum {
                    MyEnum::VariantA(x, y) => { return x + 1; },
                    MyEnum::VariantB(a) => { return a; },
                    MyEnum::VariantC => { return 3; }
                }

                return 0;
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
    }


    #[test]
    #[should_panic]
    fn test_incorrect_num_enum_pattern_data_params() {
        let scanner = Scanner::from_str("
            enum MyEnum = VariantA(a: i32, b: u32) | VariantB(a: i32) | VariantC;

            fn main() -> i32 {
                let my_enum: MyEnum = MyEnum::VariantA(a: 1, b: 2);
                match my_enum {
                    MyEnum::VariantA(x) => { return x + 1; },
                    MyEnum::VariantB(a) => { return a; },
                    MyEnum::VariantC => { return 3; }
                }

                return 0;
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
    }


    #[test]
    #[should_panic]
    fn test_incorrect_type_enum_data_params() {
        let scanner = Scanner::from_str("
            enum MyEnum = VariantA(a: i32, b: u32) | VariantB(a: i32) | VariantC;

            fn main() -> i32 {
                let my_enum: MyEnum = MyEnum::VariantA(a: 1, b: true);
                match my_enum {
                    MyEnum::VariantA(x, y) => { return x + y + 1; },
                    MyEnum::VariantB(a) => { return a; },
                    MyEnum::VariantC => { return 3; }
                }

                return 0;
            }
        ".to_owned()).unwrap();
        let mut parser = Parser::new(scanner.tokens, None);
        let ast = parser.parse().unwrap();
        Transpiler::new(ast, "test_out.cpp");
    }
}
