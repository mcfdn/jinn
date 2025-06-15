use std::fs;

use crate::{errors::JinnError, lexer::Lexer};

pub mod errors;
pub mod lexer;

fn main() -> Result<(), JinnError> {
    let source = fs::read_to_string("input.jn")?;

    let mut lexer = Lexer::new(&source);
    let tokens = lexer.lex()?;

    println!("{:#?}", tokens);

    Ok(())
}
