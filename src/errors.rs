use std::{error::Error, fmt, io};

use crate::lexer::errors::LexerError;

#[derive(Debug)]
pub enum JinnError {
    Io(io::Error),
    Lexer(LexerError),
}

impl Error for JinnError {}

impl fmt::Display for JinnError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            JinnError::Io(error) => write!(f, "io error: {error}"),
            JinnError::Lexer(error) => write!(f, "lexer error: {error}"),
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
