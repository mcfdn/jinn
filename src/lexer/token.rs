use std::{collections::HashMap, sync::LazyLock};

static KEYWORDS: LazyLock<HashMap<&'static str, KeywordKind>> = LazyLock::new(|| {
    let mut keywords = HashMap::new();
    keywords.insert("fn", KeywordKind::Function);
    keywords.insert("if", KeywordKind::If);
    keywords.insert("else", KeywordKind::Else);
    keywords.insert("for", KeywordKind::For);
    keywords.insert("let", KeywordKind::Let);
    keywords.insert("return", KeywordKind::Return);
    keywords.insert("print", KeywordKind::Print);

    keywords
});

static TYPE_ANNOTATIONS: LazyLock<HashMap<&'static str, TypeAnnotationKind>> =
    LazyLock::new(|| {
        let mut annotations = HashMap::new();
        annotations.insert("float", TypeAnnotationKind::Float);
        annotations.insert("int", TypeAnnotationKind::Int);
        annotations.insert("string", TypeAnnotationKind::String);

        annotations
    });

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub enum KeywordKind {
    Function,
    If,
    Else,
    For,
    Let,
    Return,
    Print,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum LiteralKind {
    Boolean(bool),
    Float(f64),
    Int(i64),
    String(String),
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub enum TypeAnnotationKind {
    Float,
    Int,
    String,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum TokenKind {
    Keyword(KeywordKind),
    Literal(LiteralKind),
    TypeAnnotation(TypeAnnotationKind),

    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftSquare,
    RightSquare,
    Comma,
    Dot,
    Colon,
    Semicolon,

    Plus,
    Minus,
    Slash,
    Asterisk,

    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    And,
    Or,

    Ident(String),

    Eof,
}

#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Token {
    pub kind: TokenKind,
    pub line: usize,
    pub col: usize,
}

impl Token {
    pub fn new(kind: TokenKind, line: usize, col: usize) -> Self {
        Token { kind, line, col }
    }
}

pub fn keyword_from_str(lexeme: &str) -> Option<KeywordKind> {
    KEYWORDS.get(lexeme).copied()
}

pub fn type_annotation_from_str(lexeme: &str) -> Option<TypeAnnotationKind> {
    TYPE_ANNOTATIONS.get(lexeme).copied()
}
