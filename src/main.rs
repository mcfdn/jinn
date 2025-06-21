use std::fs;

use crate::{errors::JinnError, interpreter::Interpreter, lexer::Lexer, parser::Parser};

pub mod errors;
pub mod interpreter;
pub mod lexer;
pub mod parser;

fn main() -> Result<(), JinnError> {
    let source = fs::read_to_string("input.jn")?;

    let mut lexer = Lexer::new(&source);
    let tokens = lexer.lex()?;

    let mut parser = Parser::new(tokens);
    let ast = parser.parse()?;

    let mut interpreter = Interpreter::default();
    interpreter.interpret(ast)?;

    Ok(())
}
