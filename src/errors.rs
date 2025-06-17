use std::{error::Error, fmt, io};

use crate::{lexer::errors::LexerError, parser::errors::ParserError};

#[derive(Debug)]
pub enum JinnError {
    Io(io::Error),
    Lexer(LexerError),
    Parser(ParserError),
}

impl Error for JinnError {}

impl fmt::Display for JinnError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            JinnError::Io(error) => write!(f, "io error: {error}"),
            JinnError::Lexer(error) => write!(f, "lexer error: {error}"),
            JinnError::Parser(error) => write!(f, "parser error: {error}"),
        }
    }
}

impl From<io::Error> for JinnError {
    fn from(error: io::Error) -> Self {
        JinnError::Io(error)
    }
}

impl From<LexerError> for JinnError {
    fn from(error: LexerError) -> Self {
        JinnError::Lexer(error)
    }
}

impl From<ParserError> for JinnError {
    fn from(error: ParserError) -> Self {
        JinnError::Parser(error)
    }
}
