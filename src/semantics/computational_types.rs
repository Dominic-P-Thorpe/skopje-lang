use std::error::Error;

use crate::{SyntaxNode, SyntaxTree};

use super::symbol_table::*;


#[allow(unused)]
pub fn calculate_computational_dependencies(expr: &SyntaxTree, symbol_table: &SymbolTable) -> Result<Vec<Symbol>, Box<dyn Error>> {
    Ok(match &expr.node {
        SyntaxNode::Identifier(id) => vec![symbol_table.get(&id).unwrap()],
        SyntaxNode::LeftAssocUnaryOperation(_, e)
        | SyntaxNode::RightAssocUnaryOperation(_, e)
        | SyntaxNode::SubarrayOperation(e, _, _, _)
        | SyntaxNode::ParenExpr(e) 
        | SyntaxNode::LetStmt(_, _, e)
        | SyntaxNode::TypeCast(_, _, e)
        | SyntaxNode::ReturnStmt(e) =>
            calculate_computational_dependencies(&e, symbol_table)?,
        SyntaxNode::BinaryOperation(_, l, r)
        | SyntaxNode::ArrayIndexingOperation(l, r)
        | SyntaxNode::ConcatStr(l, r)
        | SyntaxNode::WhileStmt(l, r)
        | SyntaxNode::ReassignmentStmt(l, r, _)
        | SyntaxNode::TupleIndexingOperation(l, r) => vec![
            calculate_computational_dependencies(&l, symbol_table)?,
            calculate_computational_dependencies(&r, symbol_table)?
        ].concat(),
        SyntaxNode::TernaryExpression(e, l, r)  => vec![
            calculate_computational_dependencies(&e, symbol_table)?,
            calculate_computational_dependencies(&l, symbol_table)?,
            calculate_computational_dependencies(&r, symbol_table)?
        ].concat(),
        SyntaxNode::SelectionStatement(e, l, r) => vec![
            calculate_computational_dependencies(&e, symbol_table)?,
            calculate_computational_dependencies(&l, symbol_table)?,
            match &**r {
                Some(r) => calculate_computational_dependencies(&r, symbol_table)?,
                None => vec![]
            }
        ].concat(),
        SyntaxNode::EnumInstantiation(_, _, members)
        | SyntaxNode::StructInstantiation(_, members) => 
            members.values()
                   .into_iter()
                   .map(|e| calculate_computational_dependencies(e, symbol_table).unwrap())
                   .collect::<Vec<Vec<Symbol>>>()
                   .concat(),
        SyntaxNode::ArrayLiteral(v, _)
        | SyntaxNode::TupleLiteral(v)
        | SyntaxNode::FunctionCall(_, v) => 
            v.into_iter()
             .map(|e| calculate_computational_dependencies(&e, symbol_table).unwrap())
             .collect::<Vec<Vec<Symbol>>>()
             .concat(),
        SyntaxNode::MonadicExpr(body, Some((p_id, p_type)), _) => {
            let base_dependencies = calculate_computational_dependencies(&body, symbol_table)?;
            base_dependencies.iter().filter(|d| &d.get_name() != p_id).cloned().collect()
        },
        SyntaxNode::MonadicExpr(body, None, _) => 
            calculate_computational_dependencies(&body, symbol_table)?,
        SyntaxNode::BoolLiteral(_)
        | SyntaxNode::FloatLiteral(_)
        | SyntaxNode::IntLiteral(_)
        | SyntaxNode::StringLiteral(_)
        | SyntaxNode::BreakStmt
        | SyntaxNode::ContinueStmt => vec![],
        SyntaxNode::ForStmt(i, t, expr, body) => vec![
            vec![Symbol::new(SymbolType::Variable(i.clone(), t.clone()), true, 0, 0)],
            calculate_computational_dependencies(&expr, symbol_table)?,
            calculate_computational_dependencies(&body, symbol_table)?
        ].concat(),
        SyntaxNode::MatchStmt(expr, patterns, _) => vec![
            calculate_computational_dependencies(&expr, symbol_table)?,
            patterns.into_iter()
                    .map(|(_, e)| calculate_computational_dependencies(&e, symbol_table).unwrap())
                    .collect::<Vec<Vec<Symbol>>>()
                    .concat(),
        ].concat(),
        SyntaxNode::StmtBlock(body, symbol_table) => 
            body.into_iter()
                .map(|e| calculate_computational_dependencies(&e, &symbol_table.borrow()).unwrap())
                .collect::<Vec<Vec<Symbol>>>()
                .concat(),
        SyntaxNode::SelfIdentifier => vec![
            Symbol::new(super::symbol_table::SymbolType::Variable(
                "self".to_owned(), 
                symbol_table.self_ref.as_ref().unwrap().clone()
            ), false, 0, 0)
        ],
        SyntaxNode::EnumVariant(_, _)
        | SyntaxNode::Enumeraion(_, _, _)
        | SyntaxNode::Program(_)
        | SyntaxNode::Struct(_, _, _) 
        | SyntaxNode::Function(_, _, _, _) => panic!(),
    })
}


#[cfg(test)]
mod tests {
    use std::{cell::RefCell, rc::Rc};

    use crate::{Parser, Scanner, SyntaxTree};
    use crate::parser::errors::ParsingError;
    use crate::parser::types::{SimpleType, Type};

    use super::{calculate_computational_dependencies, Symbol, SymbolTable};


    fn prepare() -> SymbolTable {
        let mut table = SymbolTable::new(None).borrow().clone();
        table.insert(Symbol::new(super::SymbolType::Variable("x".to_string(), Type::from_basic(SimpleType::I32)), false, 0, 0));
        table.insert(Symbol::new(super::SymbolType::Variable("y".to_string(), Type::from_basic(SimpleType::I32)), false, 0, 0));
        table.insert(Symbol::new(super::SymbolType::Variable("z".to_string(), Type::from_basic(SimpleType::I32)), false, 0, 0));
        table.insert(Symbol::new(super::SymbolType::Function("foo".to_string(), Type::from_basic(
            SimpleType::Function(
                Box::new(Type::from_basic(SimpleType::I32)),
                vec![Type::from_basic(SimpleType::I32), Type::from_basic(SimpleType::I32)]
            )
        )), false, 0, 0));
        table
    }


    fn get_expr_tree(parser: &mut Parser) -> SyntaxTree {
        match parser.parse_expression() {
            Ok(tree) => tree,
            Err(e) => match e {
                ParsingError::EarlyReturn(tree) => tree,
                other => panic!("{:?}", other)
            }
        }
    }
    
    
    #[test]
    fn test_single_dependency() {
        let symbol_table = prepare();

        let scanner = Scanner::from_str("x".to_string()).unwrap();
        let mut parser: Parser = Parser::new(scanner.tokens, Some(Rc::new(RefCell::new(symbol_table.clone()))));
        let tree = get_expr_tree(&mut parser);
        let dependencies = calculate_computational_dependencies(&tree, &symbol_table)
                                                            .unwrap()
                                                            .into_iter()
                                                            .map(|d| d.get_name())
                                                            .collect::<Vec<String>>();
        assert!(dependencies.contains(&"x".to_string()));
    }


    #[test]
    fn test_expression_dependency() {
        let symbol_table = prepare();

        let scanner = Scanner::from_str("x + y".to_string()).unwrap();
        let mut parser: Parser = Parser::new(scanner.tokens, Some(Rc::new(RefCell::new(symbol_table.clone()))));
        let tree = get_expr_tree(&mut parser);
        let dependencies = calculate_computational_dependencies(&tree, &symbol_table)
                                                            .unwrap()
                                                            .into_iter()
                                                            .map(|d| d.get_name())
                                                            .collect::<Vec<String>>();
        assert!(dependencies.contains(&"x".to_string()));
        assert!(dependencies.contains(&"y".to_string()));
    }


    #[test]
    fn test_monad_dependency() {
        let symbol_table = prepare();

        let scanner = Scanner::from_str("do(x: i32) { return x + y; }".to_string()).unwrap();
        let mut parser: Parser = Parser::new(scanner.tokens, Some(Rc::new(RefCell::new(symbol_table.clone()))));
        parser.current_return_type = Some(Type::from_basic(SimpleType::I32));
        let tree = get_expr_tree(&mut parser);
        let dependencies = calculate_computational_dependencies(&tree, &symbol_table)
                                                            .unwrap()
                                                            .into_iter()
                                                            .map(|d| d.get_name())
                                                            .collect::<Vec<String>>();
        assert!(!dependencies.contains(&"x".to_string()));
        assert!(dependencies.contains(&"y".to_string()));
    }


    #[test]
    fn test_complex_monad_dependency() {
        let symbol_table = prepare();

        let scanner = Scanner::from_str("do(a: i32) { 
            if (x > a) {
                return y;
            } else {
                return z; 
            }
        }".to_string()).unwrap();
        let mut parser: Parser = Parser::new(scanner.tokens, Some(Rc::new(RefCell::new(symbol_table.clone()))));
        parser.current_return_type = Some(Type::from_basic(SimpleType::I32));
        let tree = get_expr_tree(&mut parser);
        let dependencies = calculate_computational_dependencies(&tree, &symbol_table)
                                                            .unwrap()
                                                            .into_iter()
                                                            .map(|d| d.get_name())
                                                            .collect::<Vec<String>>();
        assert!(dependencies.contains(&"x".to_string()));
        assert!(dependencies.contains(&"y".to_string()));
        assert!(dependencies.contains(&"z".to_string()));
    }


    #[test]
    fn test_function_call_dependencies() {
        let symbol_table = prepare();

        let scanner = Scanner::from_str("foo(x, y)".to_string()).unwrap();
        let mut parser: Parser = Parser::new(scanner.tokens, Some(Rc::new(RefCell::new(symbol_table.clone()))));
        parser.current_return_type = Some(Type::from_basic(SimpleType::I32));
        let tree = get_expr_tree(&mut parser);
        let dependencies = calculate_computational_dependencies(&tree, &symbol_table)
                                                            .unwrap()
                                                            .into_iter()
                                                            .map(|d| d.get_name())
                                                            .collect::<Vec<String>>();
        assert!(dependencies.contains(&"x".to_string()));
        assert!(dependencies.contains(&"y".to_string()));
    }
}
