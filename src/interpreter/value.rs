use std::{
    fmt::Display,
    ops::{Add, Div, Mul, Neg, Sub},
};

use crate::interpreter::errors::InterpreterError;

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum Value {
    Boolean(bool),
    Float(f64),
    Int(i64),
    String(String),
}

impl Add for Value {
    type Output = Result<Self, InterpreterError>;

    fn add(self, rhs: Self) -> Self::Output {
        match (&self, &rhs) {
            (Value::Int(i), Value::Int(rhs)) => Ok(Value::Int(i + rhs)),
            (Value::String(s), Value::String(rhs)) => Ok(Value::String(s.clone() + rhs)),
            _ => Err(InterpreterError::RuntimeError {
                message: format!("cannot compute {} + {}", self, rhs),
            }),
        }
    }
}

impl Sub for Value {
    type Output = Result<Self, InterpreterError>;

    fn sub(self, rhs: Self) -> Self::Output {
        match (&self, &rhs) {
            (Value::Int(i), Value::Int(rhs)) => Ok(Value::Int(i - rhs)),
            _ => Err(InterpreterError::RuntimeError {
                message: format!("cannot compute {} - {}", self, rhs),
            }),
        }
    }
}

impl Div for Value {
    type Output = Result<Self, InterpreterError>;

    fn div(self, rhs: Self) -> Self::Output {
        match (&self, &rhs) {
            (Value::Int(i), Value::Int(rhs)) => Ok(Value::Int(i / rhs)),
            _ => Err(InterpreterError::RuntimeError {
                message: format!("cannot compute {} / {}", self, rhs),
            }),
        }
    }
}

impl Mul for Value {
    type Output = Result<Self, InterpreterError>;

    fn mul(self, rhs: Self) -> Self::Output {
        match (&self, &rhs) {
            (Value::Int(i), Value::Int(rhs)) => Ok(Value::Int(i * rhs)),
            _ => Err(InterpreterError::RuntimeError {
                message: format!("cannot compute {} * {}", self, rhs),
            }),
        }
    }
}

impl Neg for Value {
    type Output = Result<Self, InterpreterError>;

    fn neg(self) -> Self::Output {
        match self {
            Value::Float(f) => Ok(Value::Float(-f)),
            Value::Int(i) => Ok(Value::Int(-i)),
            _ => Err(InterpreterError::RuntimeError {
                message: "cannot apply unary negation to a non-number".to_string(),
            }),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Boolean(v) => write!(f, "{}", v),
            Value::Float(v) => write!(f, "{}", v),
            Value::Int(v) => write!(f, "{}", v),
            Value::String(v) => write!(f, "{}", v),
        }
    }
}
