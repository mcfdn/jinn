use crate::lexer::token::Token;

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Expression(Expr),
    Let(LetStmt),
    If(IfStmt),
    Block(BlockStmt),
    For(ForStmt),
    Print(PrintStmt),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Binary(Binary),
    Grouping(Grouping),
    Literal(Literal),
    Unary(Unary),
    Variable(Variable),
    Assign(Assign),
    Call(Call),
    Function(Function),
}

#[derive(Clone, Debug, PartialEq)]
pub struct LetStmt {
    pub name: Token,
    pub type_annotation: Option<Token>,
    pub initialiser: Option<Expr>,
}

impl LetStmt {
    pub fn new(name: Token, type_annotation: Option<Token>, initialiser: Option<Expr>) -> Self {
        Self {
            name,
            type_annotation,
            initialiser,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct IfStmt {
    pub condition: Expr,
    pub then_branch: Box<Stmt>,
    pub else_branch: Option<Box<Stmt>>,
}

impl IfStmt {
    pub fn new(condition: Expr, then_branch: Stmt, else_branch: Option<Stmt>) -> Self {
        Self {
            condition,
            then_branch: Box::new(then_branch),
            else_branch: else_branch.map(Box::new),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct BlockStmt {
    pub statements: Vec<Stmt>,
}

impl BlockStmt {
    pub fn new(statements: Vec<Stmt>) -> Self {
        Self { statements }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ForStmt {
    pub condition: Expr,
    pub body: Box<Stmt>,
}

impl ForStmt {
    pub fn new(condition: Expr, body: Stmt) -> Self {
        Self {
            condition,
            body: Box::new(body),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct PrintStmt {
    pub expr: Box<Expr>,
}

impl PrintStmt {
    pub fn new(expr: Expr) -> Self {
        Self {
            expr: Box::new(expr),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Binary {
    pub left: Box<Expr>,
    pub operator: Token,
    pub right: Box<Expr>,
}

impl Binary {
    pub fn new(left: Expr, operator: Token, right: Expr) -> Self {
        Self {
            left: Box::new(left),
            operator,
            right: Box::new(right),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Grouping {
    pub expr: Box<Expr>,
}

impl Grouping {
    pub fn new(expr: Expr) -> Self {
        Self {
            expr: Box::new(expr),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    Boolean(bool),
    Float(f64),
    Int(i64),
    String(String),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Unary {
    pub operator: Token,
    pub right: Box<Expr>,
}

impl Unary {
    pub fn new(operator: Token, right: Expr) -> Self {
        Self {
            operator,
            right: Box::new(right),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Variable {
    pub name: Token,
}

impl Variable {
    pub fn new(name: Token) -> Self {
        Self { name }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Assign {
    pub name: Token,
    pub value: Box<Expr>,
}

impl Assign {
    pub fn new(name: Token, value: Expr) -> Self {
        Self {
            name,
            value: Box::new(value),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Call {
    pub callee: Box<Expr>,
    pub args: Vec<Expr>,
}

impl Call {
    pub fn new(callee: Expr, args: Vec<Expr>) -> Self {
        Self {
            callee: Box::new(callee),
            args,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct FunctionParam {
    name: Token,
    type_annotation: Token,
}

impl FunctionParam {
    pub fn new(name: Token, type_annotation: Token) -> Self {
        Self {
            name,
            type_annotation,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Function {
    name: Token,
    params: Vec<FunctionParam>,
    return_type: Option<Token>,
    body: Vec<Stmt>,
}

impl Function {
    pub fn new(
        name: Token,
        params: Vec<FunctionParam>,
        return_type: Option<Token>,
        body: Vec<Stmt>,
    ) -> Self {
        Self {
            name,
            params,
            return_type,
            body,
        }
    }
}
