use std::{error::Error, fmt};

#[derive(Debug)]
pub enum LexerError {
    UnexpectedChar {
        expected: char,
        actual: char,
        line: usize,
        col: usize,
    },
    LexError {
        message: String,
        line: usize,
        col: usize,
    },
}

impl Error for LexerError {}

impl fmt::Display for LexerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedChar {
                expected,
                actual,
                line,
                col,
            } => {
                write!(
                    f,
                    "line {line}:{col}: unexpected character: expected '{expected}' but found '{actual}'",
                )
            }
            Self::LexError { message, line, col } => {
                write!(f, "line {line}:{col}: {message}")
            }
        }
    }
}
