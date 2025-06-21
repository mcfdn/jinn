use std::{error::Error, fmt};

#[derive(Debug)]
pub enum InterpreterError {
    RuntimeError { message: String },
}

impl Error for InterpreterError {}

impl fmt::Display for InterpreterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RuntimeError { message } => {
                write!(f, "{message}")
            }
        }
    }
}
