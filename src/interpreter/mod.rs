use std::collections::HashMap;

use crate::{
    interpreter::{errors::InterpreterError, value::Value},
    lexer::token::TokenKind,
    parser::ast::{
        Assign, Binary, BlockStmt, Call, Expr, ForStmt, Function, IfStmt, LetStmt, Literal, Stmt,
        Unary, Variable,
    },
};

pub mod errors;
pub mod value;

pub struct Interpreter {
    scopes: Vec<HashMap<String, Option<Value>>>,
}

impl Interpreter {
    pub fn new() -> Self {
        let mut scopes = Vec::new();
        scopes.insert(0, HashMap::new());

        Self { scopes }
    }

    pub fn interpret(&mut self, statements: Vec<Stmt>) -> Result<(), InterpreterError> {
        for statement in statements {
            self.execute(&statement)?;
        }

        Ok(())
    }

    fn execute(&mut self, statement: &Stmt) -> Result<(), InterpreterError> {
        match statement {
            Stmt::Expression(expression) => {
                self.evaluate(expression)?;
            }
            Stmt::Let(let_stmt) => {
                self.execute_let_statement(let_stmt)?;
            }
            Stmt::If(if_stmt) => {
                self.execute_if_statement(if_stmt)?;
            }
            Stmt::Block(block) => {
                self.execute_block_statement(block)?;
            }
            Stmt::For(for_stmt) => {
                self.execute_for_statement(for_stmt)?;
            }
            Stmt::Print(print) => {
                print!("{}", self.evaluate(&print.expr)?);
            }
        };

        Ok(())
    }

    fn execute_let_statement(&mut self, let_stmt: &LetStmt) -> Result<(), InterpreterError> {
        let mut value = None;
        if let Some(initialiser) = let_stmt.initialiser.clone() {
            value = Some(self.evaluate(&initialiser)?);
        }

        if let TokenKind::Ident(name) = &let_stmt.name.kind {
            self.declare_value(name, value)
        } else {
            Err(self.report_runtime_error("unexpected non-ident when executing let statement"))
        }
    }

    fn execute_if_statement(&mut self, if_stmt: &IfStmt) -> Result<(), InterpreterError> {
        let evaluation = self.evaluate(&if_stmt.condition)?;

        if let Value::Boolean(b) = evaluation {
            if b {
                // True.
                self.execute(&if_stmt.then_branch)
            } else if let Some(else_branch) = if_stmt.else_branch.clone() {
                // False, and we found an else branch.
                self.execute(&else_branch)
            } else {
                // False, but no else branch.
                Ok(())
            }
        } else {
            Err(self.report_runtime_error("unexpected non-bool when executing if statement"))
        }
    }

    fn execute_block_statement(&mut self, block: &BlockStmt) -> Result<(), InterpreterError> {
        self.push_scope();

        for statement in &block.statements {
            self.execute(statement)?;
        }

        self.pop_scope();

        Ok(())
    }

    fn execute_for_statement(&mut self, for_stmt: &ForStmt) -> Result<(), InterpreterError> {
        loop {
            let evaluation = self.evaluate(&for_stmt.condition)?;

            if let Value::Boolean(b) = evaluation {
                if b {
                    self.execute(&for_stmt.body)?;
                } else {
                    break;
                }
            } else {
                return Err(
                    self.report_runtime_error("unexpected non-bool when executing for statement")
                );
            }
        }

        Ok(())
    }

    fn evaluate(&mut self, expression: &Expr) -> Result<Value, InterpreterError> {
        match expression {
            Expr::Binary(binary) => self.evaluate_binary_expression(binary),
            Expr::Grouping(grouping) => self.evaluate(&grouping.expr),
            Expr::Literal(literal) => Ok(self.evaluate_literal_expression(literal)),
            Expr::Unary(unary) => self.evaluate_unary_expression(unary),
            Expr::Variable(variable) => self.evaluate_variable_expression(variable),
            Expr::Assign(assign) => self.evaluate_assign_expression(assign),
            Expr::Call(call) => Ok(self.evaluate_call_expression(call)),
            Expr::Function(function) => Ok(self.evaluate_function_expression(function)),
        }
    }

    fn evaluate_binary_expression(&mut self, binary: &Binary) -> Result<Value, InterpreterError> {
        let left = self.evaluate(&binary.left)?;
        let right = self.evaluate(&binary.right)?;

        match (left, right, binary.operator.kind.clone()) {
            // Binary operators.
            (a, b, TokenKind::Plus) => a + b,
            (a, b, TokenKind::Minus) => a - b,
            (a, b, TokenKind::Slash) => a / b,
            (a, b, TokenKind::Asterisk) => a * b,

            // Comparison operators.
            (a, b, TokenKind::Greater) => Ok(Value::Boolean(a > b)),
            (a, b, TokenKind::GreaterEqual) => Ok(Value::Boolean(a >= b)),
            (a, b, TokenKind::Less) => Ok(Value::Boolean(a < b)),
            (a, b, TokenKind::LessEqual) => Ok(Value::Boolean(a <= b)),

            // Equality operators.
            (a, b, TokenKind::BangEqual) => Ok(Value::Boolean(a != b)),
            (a, b, TokenKind::EqualEqual) => Ok(Value::Boolean(a == b)),

            _ => Err(self.report_runtime_error("unsupported binary expression")),
        }
    }

    fn evaluate_literal_expression(&self, literal: &Literal) -> Value {
        match literal {
            Literal::Boolean(v) => Value::Boolean(*v),
            Literal::Float(v) => Value::Float(*v),
            Literal::Int(v) => Value::Int(*v),
            Literal::String(v) => Value::String(v.clone()),
        }
    }

    fn evaluate_unary_expression(&mut self, unary: &Unary) -> Result<Value, InterpreterError> {
        let right = self.evaluate(&unary.right)?;

        match unary.operator.kind {
            TokenKind::Minus => -right,
            _ => Err(self.report_runtime_error("only unary negations are supported")),
        }
    }

    fn evaluate_variable_expression(&self, variable: &Variable) -> Result<Value, InterpreterError> {
        if let TokenKind::Ident(name) = &variable.name.kind {
            self.get_value(name)
        } else {
            Err(self.report_runtime_error(
                "encountered non-identifier token when evaluating variable expression",
            ))
        }
    }

    fn evaluate_assign_expression(&mut self, assign: &Assign) -> Result<Value, InterpreterError> {
        if let TokenKind::Ident(name) = &assign.name.kind {
            let value = self.evaluate(&assign.value)?;
            self.assign_value(name, value.clone())?;

            Ok(value)
        } else {
            Err(self.report_runtime_error(
                "encountered non-identifier token when evaluating assignment expression",
            ))
        }
    }

    fn evaluate_call_expression(&self, _call: &Call) -> Value {
        todo!();
    }

    fn evaluate_function_expression(&self, _function: &Function) -> Value {
        todo!()
    }

    fn declare_value(&mut self, key: &str, value: Option<Value>) -> Result<(), InterpreterError> {
        if let Some(env) = self.scopes.last_mut() {
            env.insert(key.to_string(), value);
            Ok(())
        } else {
            Err(self.report_runtime_error(
                "failed to resolve the current scope when declaring a variable",
            ))
        }
    }

    fn assign_value(&mut self, key: &str, value: Value) -> Result<(), InterpreterError> {
        for env in self.scopes.iter_mut().rev() {
            if env.contains_key(key) {
                env.insert(key.to_string(), Some(value));
                return Ok(());
            }
        }

        Err(self.report_runtime_error(&format!("use of undefined identifier: {key}")))
    }

    fn get_value(&self, key: &str) -> Result<Value, InterpreterError> {
        for env in self.scopes.iter().rev() {
            if let Some(declaration) = env.get(key) {
                if let Some(value) = declaration {
                    return Ok(value.clone());
                } else {
                    return Err(self
                        .report_runtime_error(&format!("use of uninitialised identifier: {key}")));
                }
            }
        }

        Err(self.report_runtime_error(&format!("use of undefined identifier: {key}")))
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn report_runtime_error(&self, message: &str) -> InterpreterError {
        InterpreterError::RuntimeError {
            message: message.to_string(),
        }
    }
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}
