use core::fmt;
use std::error::Error;

#[derive(Debug)]
pub enum ParserError {
    ParseError {
        message: String,
        line: usize,
        col: usize,
    },
}

impl Error for ParserError {}

impl fmt::Display for ParserError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!();
    }
}
