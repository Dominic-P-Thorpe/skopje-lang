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
//!     let mut parser = Parser::new(scanner.tokens);
//!     let ast = parser.parse().unwrap();
//!     let mut transpiler = Transpiler::new(ast, "out.c");
//! }
//! ``` 
use indexmap::IndexMap;
use rand::distributions::{Alphanumeric, DistString};
use std::error::Error;
use std::fs::{File, OpenOptions};
use std::io::Write;

use crate::parser::types::{Type, SimpleType};
use crate::semantics::typechecking::{fold_constexpr_index, get_array_inner_type};
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
    /// let mut parser = Parser::new(scanner.tokens);
    /// let ast = parser.parse().unwrap();
    /// let mut transpiler = Transpiler::new(ast, "out.c");
    /// ```
    pub fn new(source: SyntaxTree, target: &str) -> Self {
        Transpiler { 
            file: OpenOptions::new().create(true).truncate(true).write(true).open(target).unwrap(), 
            functions_source: vec![],
            auxilliary_func_index: 0,
            ast: source 
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
            let mut statements_text: String = String::new();
            for statement in statements {
                statements_text += &self.transpile_c_tree(statement, 0)?;
            }

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
            SyntaxNode::Function(name, args, return_type, body) => {
                let args_string = args.iter()
                                      .map(|(p_id, p_type)| format!("{} {}", p_type.basic_type.as_ctype_str(), p_id))
                                      .collect::<Vec<String>>()
                                      .join(", ");
                let return_type_text = return_type.as_ctype_str();
                let body_text = body.iter()
                                    .map(|s| self.transpile_c_tree(s, indent + 1).unwrap())
                                    .collect::<Vec<String>>()
                                    .join("\n");
                
                // main function is a special case as it must have the return type of "int", so we
                // convert this function's name to a different name (__special__main())
                if name.as_str() == "main" {
                    return Ok(format!("\n{} __special__main() {{\n{} \n}}\n\n", return_type_text, body_text));
                }

                Ok(format!("\n{} {}({}) {{\n{} \n}}\n\n", return_type_text, name, args_string, body_text))
            }

            SyntaxNode::ReturnStmt(body) => {
                let body_text = self.transpile_typed_expr_c(&body, &Type::from_basic(SimpleType::Void))?;
                Ok("    ".repeat(indent) + "return " + &body_text + ";")
            }

            SyntaxNode::Program(_) => panic!("Got program when I should not have!"),

            SyntaxNode::FunctionCallStmt(func_id, args) => {
                let args: Vec<String> = args.iter()
                                            .map(|arg| self.transpile_typed_expr_c(arg, &Type::from_basic(SimpleType::Void)).unwrap())
                                            .collect();
                if func_id == "print" {
                    return Ok(format!("{}printf({});", "    ".repeat(indent), args.first().unwrap()));
                } else if func_id == "readln" {
                    return Ok(format!("{}readln({});", "    ".repeat(indent), args.first().unwrap()));
                }

                Ok(format!("{}{}({});", "    ".repeat(indent), func_id, args.join(", ")))
            },

            SyntaxNode::SelectionStatement(cond, if_body, None) => {
                Ok(format!(
                    "{0}if ({1}) {{\n{2}\n{0}}}",
                    "    ".repeat(indent), 
                    self.transpile_typed_expr_c(cond, &Type::from_basic(SimpleType::Bool))?,
                    if_body.iter()
                           .map(|s| self.transpile_c_tree(s, indent + 1).unwrap())
                           .collect::<Vec<String>>()
                           .join("\n")
                )) 
            }

            SyntaxNode::SelectionStatement(cond, if_body, Some(else_body)) => {
                Ok(format!(
                    "{0}if ({1}) {{\n{2}\n{0}}} else {{\n{3}\n{0}}}", 
                    "    ".repeat(indent), 
                    self.transpile_typed_expr_c(cond, &Type::from_basic(SimpleType::Bool))?,
                    if_body.iter()
                           .map(|s| self.transpile_c_tree(s, indent + 1).unwrap())
                           .collect::<Vec<String>>()
                           .join("\n"),
                    else_body.iter()
                             .map(|s| self.transpile_c_tree(s, indent + 1).unwrap())
                             .collect::<Vec<String>>()
                             .join("\n")
                )) 
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
                    body.iter()
                        .map(|s| self.transpile_c_tree(s, indent + 1).unwrap())
                        .collect::<Vec<String>>()
                        .join("\n")
                ))
            }
            
            SyntaxNode::WhileStmt(cond, body) => {
                Ok(format!(
                    "{0}while ({1}) {{\n{2}{0}\n{0}}}\n", 
                    "    ".repeat(indent),
                    self.transpile_typed_expr_c(cond, &Type::from_basic(SimpleType::Bool))?,
                    body.iter()
                        .map(|s| self.transpile_c_tree(s, indent + 1).unwrap())
                        .collect::<Vec<String>>()
                        .join("\n")
                ))
            }

            SyntaxNode::LetStmt(id, var_type, expr) => Ok(format!(
                "{}{} {} = {};",
                "    ".repeat(indent), 
                var_type.as_ctype_str(), 
                id, 
                self.transpile_typed_expr_c(expr, var_type)?
            )),

            SyntaxNode::ReassignmentStmt(id, expr, var_type) => Ok(format!(
                "{}{} = {};",
                "    ".repeat(indent), 
                self.transpile_typed_expr_c(id, var_type)?,
                self.transpile_typed_expr_c(expr, var_type)?
            )),

            SyntaxNode::MonadicExpr(body) => {
                let monad_func_name = self.get_next_auxilliary_func_name();
                let body_code: String = body.iter()
                                            .map(|s| self.transpile_c_tree(s, 1).unwrap())
                                            .collect::<String>();
                self.functions_source.push(
                    format!("void {}() {{\n{}\n}}", monad_func_name, body_code)
                );
                
                Ok(format!("IOMonad<void(*)()>::lift({})", monad_func_name))
            }

            SyntaxNode::MatchStmt(_, _, _) => self.transpile_match_stmt(tree, indent),

            SyntaxNode::Enumeraion(name, variants) => self.transpile_enum(name, variants, indent),
            other => panic!("{:?} is not a valid node!", other)
        }
    }


    fn transpile_match_stmt(&mut self, tree: &SyntaxTree, indent: usize) -> Result<String, Box<dyn Error>> {
        // TODO: adapt this to take non-enum expression types
        if let SyntaxNode::MatchStmt(match_expr, patterns, match_type) = &tree.node {
            assert!(patterns.len() > 0);
            let match_expr_str = self.transpile_typed_expr_c(&*match_expr, &match_type)?;
            return Ok(format!(
                "{0}switch ({1}.getTag()) {{\n{2}\n{0}}}", 
                "    ".repeat(indent),
                match_expr_str,
                self.transpile_patterns(&patterns, &match_expr_str, indent + 1)?
            ));
        }
        
        panic!("Expected match statement, got {:?}", tree)
    }


    fn transpile_patterns(&mut self, patterns: &Vec<(Vec<Pattern>, Vec<SyntaxTree>)>, match_expr_str: &str, indent: usize) -> Result<String, Box<dyn Error>> {
        let mut patterns_strs: Vec<String> = vec![];
        for (pattern, body) in patterns {
            // get the first pattern in the list of patterns to match against
            let pattern = pattern.get(0).unwrap();
            match pattern {
                Pattern::EnumPattern(enum_name, variant_name, _) => patterns_strs.push(format!(
                    "{0}case {1}::{2}: {{\n{0}\t{1}::InternalUnion::{4} iu = {5}.getValue().{6};\n{3}\n\t{0}break;\n{0}}}",
                    "    ".repeat(indent),
                    enum_name,
                    variant_name,
                    // transpile the body of the pattern branch
                    body.iter().map(|stmt| self.transpile_c_tree(stmt, indent + 1).unwrap()).collect::<Vec<String>>().join("\n"),
                    capitalize(variant_name),
                    match_expr_str,
                    variant_name.to_lowercase()
                )),
                
                Pattern::IdentifierPattern(id) => patterns_strs.push(format!(
                    "{0}default: {{\n\t{0}auto {1} = {2}.getValue();\n\t{0}break;\n{0}}}", 
                    "    ".repeat(indent),
                    id, match_expr_str
                ))
            }
        }

        // join the pattern branches together
        Ok(patterns_strs.join("\n\n"))
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
                    "->" => Ok(format!("{}.arrow({}.bind())", self.transpile_typed_expr_c(l, target)?, self.transpile_typed_expr_c(r, target)?)),
                    ".." => {
                        let start = fold_constexpr_index(&l);
                        let end = fold_constexpr_index(&r);
                        Ok(format!("array_range<{}, {}>({}, {})", get_array_inner_type(&target).as_ctype_str(), usize::abs_diff(start, end), start, end))
                    }
                    _ => Ok(format!("{} {} {}", self.transpile_typed_expr_c(l, target)?, op, self.transpile_typed_expr_c(l, target)?)) 
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

            SyntaxNode::SubarrayOperation(root, root_type, start, end) => {
                match &root_type.basic_type {
                    SimpleType::Array(_, len) => 
                        Ok(format!("subarray<{0}, {1}, {2}, {3}>({4}, {2}, {3})", get_array_inner_type(&target).as_ctype_str(), len, start, end, self.transpile_typed_expr_c(root, target)?)),
                    other => panic!("Expected array, got {:?}", other)
                }
            }

            SyntaxNode::FunctionCall(func_id, args) => {
                let args: Vec<String> = args.iter()
                                            .map(|arg| self.transpile_typed_expr_c(arg, &Type::from_basic(SimpleType::Void)).unwrap())
                                            .collect();
                if func_id == &String::from("print") {
                    return Ok(format!("printf({})", args.first().unwrap()));
                }

                Ok(format!("{}({})", func_id, &args.join(", ")))
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
                    3,
                    elems.iter()
                         .map(|e| self.transpile_typed_expr_c(e, &get_array_inner_type(&target)).unwrap())
                         .collect::<Vec<String>>()
                         .join(", ")
                ))
            }

            SyntaxNode::EnumInstantiation(enum_type, variant, args) => match &enum_type.basic_type {
                SimpleType::Enum(name, variants, _) => {
                    let variant_data: &IndexMap<String, Type> = variants.get(variant).unwrap();
                    let args_str = args.values()
                                       .map(|v| self.transpile_typed_expr_c(&v, &Type::from_basic(SimpleType::I32)).unwrap())
                                       .collect::<Vec<String>>().join(", ");
                    
                    if variant_data.len() == 0 {
                        Ok(format!("{}({})", name, variants.get_index_of(variant).unwrap()))
                    } else {
                        Ok(format!("{}({}, {})", name, variants.get_index_of(variant).unwrap(), args_str))
                    }
                }
                _ => panic!()
            }

            other => panic!("{:?} is not a valid expression node!", other)
        }
    }


    fn transpile_enum(&self, name: &String, variants: &Vec<SyntaxTree>, indent: usize) -> Result<String, Box<dyn Error>> {
        let string = format!("
class {0} {{
public:
    enum Tag {{
        {1}
    }};

    union InternalUnion {{
        {2}
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
                    SyntaxNode::EnumVariant(name, _) => format!("
            case {0}:
                this->value.{1} = create_struct<InternalUnion::{0}>(args...);
                break;
", 
                        capitalize(name), 
                        name.to_lowercase()
                    ),
                    _ => panic!()
                }
            ).collect::<Vec<String>>().join(&format!("\t\t{}", "    ".repeat(indent)))
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
    use crate::parser::parsing::Parser;
    use crate::parser::lexing::Scanner;
    use super::Transpiler;


    #[test]
    fn test_for_loop() {
        let scanner = Scanner::new("tests/test_for_loop.skj").unwrap();
        let mut parser = Parser::new(scanner.tokens);
        match parser.parse() {
            Err(e) => eprintln!("{}", e),
            Ok(ast) => {
                let mut transpiler = Transpiler::new(ast, "test_out.cpp");
                println!("{:#?}", transpiler.transpile_c());
            }
        }
    }
}
