use std::{collections::HashMap, fmt::Display};

use crate::{
    interpreter::{errors::InterpreterError, value::Value},
    lexer::token::TokenKind,
    parser::ast::{
        Assign, Binary, BlockStmt, Call, Expr, ForStmt, Function, IfStmt, LetStmt, Literal,
        ReturnStmt, Stmt, Unary, Variable,
    },
};

pub mod errors;
pub mod value;

// ExecSignal represents the result of executing a statement or block, and signals how the
// evaluation should be propagated up the call stack.
enum ExecSignal {
    // Normal indicates that execution completed without a return statement.
    Normal,
    // Return represents a return from a function or other block, optionally containing a value.
    Return(Option<Value>),
}

pub struct Interpreter {
    scopes: Vec<HashMap<String, Option<Value>>>,
}

impl Interpreter {
    pub fn new() -> Self {
        let mut scopes = Vec::new();
        scopes.push(HashMap::new());

        Self { scopes }
    }

    pub fn interpret(&mut self, statements: Vec<Stmt>) -> Result<(), InterpreterError> {
        for statement in statements {
            self.execute(&statement)?;
        }

        Ok(())
    }

    fn execute(&mut self, statement: &Stmt) -> Result<ExecSignal, InterpreterError> {
        match statement {
            Stmt::Expression(expression) => {
                self.evaluate(expression)?;
                Ok(ExecSignal::Normal)
            }
            Stmt::Let(let_stmt) => {
                self.execute_let_statement(let_stmt)?;
                Ok(ExecSignal::Normal)
            }
            Stmt::If(if_stmt) => self.execute_if_statement(if_stmt),
            Stmt::Block(block) => self.execute_block_statement(block),
            Stmt::For(for_stmt) => self.execute_for_statement(for_stmt),
            Stmt::Print(print) => {
                print!("{}", self.evaluate(&print.expr)?);
                Ok(ExecSignal::Normal)
            }
            Stmt::Return(return_stmt) => self.execute_return_statement(return_stmt),
        }
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

    fn execute_if_statement(&mut self, if_stmt: &IfStmt) -> Result<ExecSignal, InterpreterError> {
        let evaluation = self.evaluate(&if_stmt.condition)?;

        if let Value::Boolean(b) = evaluation {
            if b {
                // True.
                self.execute(&if_stmt.then_branch)
            } else if let Some(ref else_branch) = if_stmt.else_branch {
                // False, and we found an else branch.
                self.execute(else_branch)
            } else {
                // False, but no else branch.
                Ok(ExecSignal::Normal)
            }
        } else {
            Err(self.report_runtime_error("unexpected non-bool when executing if statement"))
        }
    }

    fn execute_block_statement(
        &mut self,
        block: &BlockStmt,
    ) -> Result<ExecSignal, InterpreterError> {
        self.push_scope();
        let signal = self.execute_statements(&block.statements)?;
        self.pop_scope();

        Ok(signal)
    }

    fn execute_statements(&mut self, statements: &[Stmt]) -> Result<ExecSignal, InterpreterError> {
        for statement in statements {
            match self.execute(&statement)? {
                ExecSignal::Normal => {}
                ExecSignal::Return(v) => {
                    // Early exit out of block.
                    return Ok(ExecSignal::Return(v));
                }
            }
        }

        Ok(ExecSignal::Normal)
    }

    fn execute_for_statement(
        &mut self,
        for_stmt: &ForStmt,
    ) -> Result<ExecSignal, InterpreterError> {
        loop {
            let evaluation = self.evaluate(&for_stmt.condition)?;

            if let Value::Boolean(b) = evaluation {
                if b {
                    match self.execute(&for_stmt.body)? {
                        ExecSignal::Normal => {}
                        ExecSignal::Return(v) => {
                            // Early exit out of block.
                            return Ok(ExecSignal::Return(v));
                        }
                    }
                } else {
                    break;
                }
            } else {
                return Err(
                    self.report_runtime_error("unexpected non-bool when executing for statement")
                );
            }
        }

        Ok(ExecSignal::Normal)
    }

    fn execute_return_statement(
        &mut self,
        return_stmt: &ReturnStmt,
    ) -> Result<ExecSignal, InterpreterError> {
        let value = if let Some(expr) = &return_stmt.expr {
            Some(self.evaluate(expr)?)
        } else {
            None
        };

        Ok(ExecSignal::Return(value))
    }

    fn evaluate(&mut self, expression: &Expr) -> Result<Value, InterpreterError> {
        match expression {
            Expr::Binary(binary) => self.evaluate_binary_expression(binary),
            Expr::Grouping(grouping) => self.evaluate(&grouping.expr),
            Expr::Literal(literal) => Ok(self.evaluate_literal_expression(literal)),
            Expr::Unary(unary) => self.evaluate_unary_expression(unary),
            Expr::Variable(variable) => self.evaluate_variable_expression(variable),
            Expr::Assign(assign) => self.evaluate_assign_expression(assign),
            Expr::Call(call) => self.evaluate_call_expression(call),
            Expr::Function(function) => self.evaluate_function_expression(function),
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

    fn evaluate_call_expression(&mut self, call: &Call) -> Result<Value, InterpreterError> {
        let callee = self.evaluate(&call.callee)?;

        let arguments = call
            .args
            .iter()
            .map(|a| self.evaluate(a))
            .collect::<Result<Vec<_>, _>>()?;

        // TODO: Validate arity.

        match callee {
            Value::Callable(c) => c.call(self, arguments),
            v => Err(self
                .report_runtime_error(&format!("attempted to call non-function value: {:?}", v))),
        }
    }

    fn evaluate_function_expression(
        &mut self,
        function: &Function,
    ) -> Result<Value, InterpreterError> {
        let callable = CallableFunction::new(function.clone());

        if let TokenKind::Ident(name) = &function.name.kind {
            self.declare_value(name, Some(Value::Callable(callable.clone())))?;
        } else {
            return Err(
                self.report_runtime_error("unexpected non-ident when executing function statement")
            );
        }

        Ok(Value::Callable(callable))
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

trait Callable {
    fn call(
        self,
        interpreter: &mut Interpreter,
        args: Vec<Value>,
    ) -> Result<Value, InterpreterError>;
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct CallableFunction {
    function: Function,
}

impl CallableFunction {
    fn new(function: Function) -> Self {
        Self { function }
    }
}

impl Callable for CallableFunction {
    fn call(
        self,
        interpreter: &mut Interpreter,
        args: Vec<Value>,
    ) -> Result<Value, InterpreterError> {
        interpreter.push_scope();

        for (i, param) in self.function.params.iter().enumerate() {
            match &param.name.kind {
                TokenKind::Ident(identifier) => {
                    if let Some(value) = args.get(i) {
                        let _ = interpreter.declare_value(identifier, Some(value.clone()));
                    } else {
                        return Err(interpreter.report_runtime_error(&format!(
                            "missing argument for parameter {:?}",
                            identifier
                        )));
                    }
                }
                v => {
                    return Err(interpreter
                        .report_runtime_error(&format!("invalid function parameter: {:?}", v)));
                }
            }
        }

        let result = interpreter.execute_statements(&self.function.body);

        interpreter.pop_scope();

        match result? {
            ExecSignal::Normal => Ok(Value::Unit),
            ExecSignal::Return(Some(value)) => Ok(value),
            ExecSignal::Return(None) => Ok(Value::Unit),
        }
    }
}

impl Display for CallableFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "function {:?}", self.function)
    }
}
