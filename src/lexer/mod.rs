pub mod errors;
pub mod token;

use std::{iter::Peekable, str::CharIndices};

use token::{LiteralKind, Token, TokenKind, keyword_from_str, type_annotation_from_str};

use crate::lexer::errors::LexerError;

const NUL_BYTE: char = '\0';

pub struct Lexer<'a> {
    source: &'a str,
    chars: Peekable<CharIndices<'a>>,
    current_pos: usize,
    current_line: usize,
    current_col: usize,
    token_start_pos: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Self {
        Lexer {
            source,
            chars: source.char_indices().peekable(),
            current_pos: 0,
            current_line: 1,
            current_col: 1,
            token_start_pos: 0,
        }
    }

    pub fn lex(&mut self) -> Result<Vec<Token>, LexerError> {
        let mut tokens = Vec::new();

        loop {
            let token = self.next_token()?;
            let is_eof = token.kind == TokenKind::Eof;

            tokens.push(token);

            if is_eof {
                break;
            }
        }

        Ok(tokens)
    }

    fn next_token(&mut self) -> Result<Token, LexerError> {
        let ch = self.advance();
        self.token_start_pos = self.current_pos;

        match ch {
            Some(ch) => match ch {
                '(' => Ok(self.create_token(TokenKind::LeftParen)),
                ')' => Ok(self.create_token(TokenKind::RightParen)),
                '{' => Ok(self.create_token(TokenKind::LeftBrace)),
                '}' => Ok(self.create_token(TokenKind::RightBrace)),
                '[' => Ok(self.create_token(TokenKind::LeftSquare)),
                ']' => Ok(self.create_token(TokenKind::RightSquare)),
                ',' => Ok(self.create_token(TokenKind::Comma)),
                '.' => Ok(self.create_token(TokenKind::Dot)),
                '+' => Ok(self.create_token(TokenKind::Plus)),
                ':' => Ok(self.create_token(TokenKind::Colon)),
                ';' => Ok(self.create_token(TokenKind::Semicolon)),
                '*' => Ok(self.create_token(TokenKind::Asterisk)),

                '!' => Ok(self.lex_bang_or_bang_equal()),
                '=' => Ok(self.lex_equal_or_equal_equal()),
                '>' => Ok(self.lex_greater_or_greater_equal()),
                '<' => Ok(self.lex_less_or_less_equal()),
                '-' => self.lex_minus_or_number(),

                '&' => self.lex_and(),
                '|' => self.lex_or(),
                '"' => self.lex_string(),
                '/' => self.lex_slash_or_eat_comment(),

                ch if Self::is_line_terminator(ch) => {
                    self.eat_newline(ch);
                    self.next_token()
                }

                ch if Self::is_whitespace(ch) => self.next_token(),
                ch if Self::is_digit(ch) => self.lex_number(),
                ch if Self::is_alpha(ch) => Ok(self.lex_keyword_type_annotation_or_bool()),

                _ => Err(self.report_lex_error("unexpected lexeme")),
            },

            None => Ok(self.create_token(TokenKind::Eof)),
        }
    }

    fn advance(&mut self) -> Option<char> {
        if let Some((pos, ch)) = self.chars.next() {
            self.current_pos = pos;
            self.current_col += 1;
            return Some(ch);
        }
        None
    }

    fn advance_if(&mut self, ch: char) -> bool {
        if let Some(next_ch) = self.peek() {
            if next_ch == ch {
                self.advance();
                return true;
            }
        }
        false
    }

    fn peek(&mut self) -> Option<char> {
        if let Some((_, ch)) = self.chars.peek().copied() {
            return Some(ch);
        }
        None
    }

    fn eat_newline(&mut self, ch: char) {
        if ch == '\r' && self.peek() == Some('\n') {
            // Handle \r\n by advancing over the \n and only incrementing
            // num_lines once.
            self.advance();
        }
        self.current_line += 1;
        self.current_col = 1;
    }

    fn lex_number(&mut self) -> Result<Token, LexerError> {
        let mut found_decimal_point = false;
        while let Some(ch) = self.peek() {
            if !Self::is_digit(ch) && ch != '.' && ch != '_' {
                break;
            }

            if ch == '.' {
                if found_decimal_point {
                    return Err(
                        self.report_lex_error("found number with more than one decimal point")
                    );
                }

                found_decimal_point = true;
            }

            self.advance();
        }

        let lexeme = &self.source[self.token_start_pos..=self.current_pos];
        let literal = lexeme.replace('_', "");

        if found_decimal_point {
            // Floating point number.
            return if let Ok(parsed_literal) = literal.parse::<f64>() {
                Ok(self.create_token(TokenKind::Literal(LiteralKind::Float(parsed_literal))))
            } else {
                Err(self.report_lex_error("unable to parse float"))
            };
        }

        // Integer.
        if let Ok(parsed_literal) = literal.parse::<i64>() {
            Ok(self.create_token(TokenKind::Literal(LiteralKind::Int(parsed_literal))))
        } else {
            Err(self.report_lex_error("unable to parse unsigned integer"))
        }
    }

    fn lex_string(&mut self) -> Result<Token, LexerError> {
        while let Some(ch) = self.peek() {
            if ch == '"' {
                break;
            }

            if Self::is_line_terminator(ch) {
                self.eat_newline(ch);
            }

            self.advance();
        }

        if self.peek().is_none() {
            return Err(self.report_lex_error("unterminated string encountered"));
        }

        // Eat the closing quote.
        self.advance();

        Ok(self.create_token(TokenKind::Literal(LiteralKind::String(
            self.source[self.token_start_pos + 1..self.current_pos].to_string(),
        ))))
    }

    fn lex_slash_or_eat_comment(&mut self) -> Result<Token, LexerError> {
        // If we don't find another '/', return a Slash token.
        if !self.advance_if('/') {
            return Ok(self.create_token(TokenKind::Slash));
        }

        // We found another '/', so treat everything up to a newline as a comment.
        while let Some(ch) = self.peek() {
            if ch == '\n' {
                break;
            }
            self.advance();
        }

        self.next_token()
    }

    fn lex_keyword_type_annotation_or_bool(&mut self) -> Token {
        while let Some(ch) = self.peek() {
            if !Self::is_alphanum(ch) {
                break;
            }
            self.advance();
        }

        let lexeme = &self.source[self.token_start_pos..=self.current_pos];

        if lexeme == "true" {
            return self.create_token(TokenKind::Literal(LiteralKind::Boolean(true)));
        }

        if lexeme == "false" {
            return self.create_token(TokenKind::Literal(LiteralKind::Boolean(false)));
        }

        if let Some(keyword) = keyword_from_str(lexeme) {
            return self.create_token(TokenKind::Keyword(keyword));
        }

        if let Some(type_annotation) = type_annotation_from_str(lexeme) {
            return self.create_token(TokenKind::TypeAnnotation(type_annotation));
        }

        self.create_token(TokenKind::Ident(lexeme.to_string()))
    }

    fn lex_bang_or_bang_equal(&mut self) -> Token {
        if self.advance_if('=') {
            return self.create_token(TokenKind::BangEqual);
        }

        self.create_token(TokenKind::Bang)
    }

    fn lex_equal_or_equal_equal(&mut self) -> Token {
        if self.advance_if('=') {
            return self.create_token(TokenKind::EqualEqual);
        }

        self.create_token(TokenKind::Equal)
    }

    fn lex_greater_or_greater_equal(&mut self) -> Token {
        if self.advance_if('=') {
            return self.create_token(TokenKind::GreaterEqual);
        }

        self.create_token(TokenKind::Greater)
    }

    fn lex_less_or_less_equal(&mut self) -> Token {
        if self.advance_if('=') {
            return self.create_token(TokenKind::LessEqual);
        }

        self.create_token(TokenKind::Less)
    }

    fn lex_minus_or_number(&mut self) -> Result<Token, LexerError> {
        if let Some(peeked) = self.peek() {
            if Self::is_digit(peeked) {
                return self.lex_number();
            }
        }

        Ok(self.create_token(TokenKind::Minus))
    }

    fn lex_and(&mut self) -> Result<Token, LexerError> {
        if !self.advance_if('&') {
            return Err(self.report_unexpected_char('&'));
        }

        Ok(self.create_token(TokenKind::And))
    }

    fn lex_or(&mut self) -> Result<Token, LexerError> {
        if !self.advance_if('|') {
            return Err(self.report_unexpected_char('|'));
        }

        Ok(self.create_token(TokenKind::Or))
    }

    fn create_token(&self, kind: TokenKind) -> Token {
        Token::new(kind, self.current_line, self.current_col)
    }

    fn report_unexpected_char(&mut self, expected: char) -> LexerError {
        LexerError::UnexpectedChar {
            expected,
            actual: self.peek().unwrap_or(NUL_BYTE),
            line: self.current_line,
            col: self.current_col - 1,
        }
    }

    fn report_lex_error(&mut self, message: &str) -> LexerError {
        LexerError::LexError {
            message: message.to_string(),
            line: self.current_line,
            col: self.current_col,
        }
    }

    fn is_line_terminator(ch: char) -> bool {
        ch == '\r' || ch == '\n'
    }

    fn is_whitespace(ch: char) -> bool {
        ch == ' ' || ch == '\t'
    }

    fn is_digit(ch: char) -> bool {
        ch.is_ascii_digit()
    }

    fn is_alpha(ch: char) -> bool {
        ch.is_ascii_lowercase() || ch.is_ascii_uppercase() || ch == '_'
    }

    fn is_alphanum(ch: char) -> bool {
        Self::is_alpha(ch) || Self::is_digit(ch)
    }
}

#[cfg(test)]
mod tests {
    use token::TypeAnnotationKind;

    use crate::lexer::token::KeywordKind;

    use super::*;

    #[test]
    fn scan_token_creates_correct_token() {
        let input = r#"

// This is a comment that spans...
//
// ...a few lines.

(){}[],.:;
+-/*
! != = == > >= < <=
&& ||
fn if else for let return true false
"my string"
"multi-
line string"
"multibyte 😊"
12345
12_345
-12345
-12_345
123.456
12_345.67
-123.456
-12_345.67
my_ident
my_2nd_ident
string
"#;

        let expected = vec![
            TokenKind::LeftParen,
            TokenKind::RightParen,
            TokenKind::LeftBrace,
            TokenKind::RightBrace,
            TokenKind::LeftSquare,
            TokenKind::RightSquare,
            TokenKind::Comma,
            TokenKind::Dot,
            TokenKind::Colon,
            TokenKind::Semicolon,
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Slash,
            TokenKind::Asterisk,
            TokenKind::Bang,
            TokenKind::BangEqual,
            TokenKind::Equal,
            TokenKind::EqualEqual,
            TokenKind::Greater,
            TokenKind::GreaterEqual,
            TokenKind::Less,
            TokenKind::LessEqual,
            TokenKind::And,
            TokenKind::Or,
            TokenKind::Keyword(KeywordKind::Function),
            TokenKind::Keyword(KeywordKind::If),
            TokenKind::Keyword(KeywordKind::Else),
            TokenKind::Keyword(KeywordKind::For),
            TokenKind::Keyword(KeywordKind::Let),
            TokenKind::Keyword(KeywordKind::Return),
            TokenKind::Literal(LiteralKind::Boolean(true)),
            TokenKind::Literal(LiteralKind::Boolean(false)),
            TokenKind::Literal(LiteralKind::String("my string".to_string())),
            TokenKind::Literal(LiteralKind::String("multi-\nline string".to_string())),
            TokenKind::Literal(LiteralKind::String("multibyte 😊".to_string())),
            TokenKind::Literal(LiteralKind::Int(12345)),
            TokenKind::Literal(LiteralKind::Int(12345)),
            TokenKind::Literal(LiteralKind::Int(-12345)),
            TokenKind::Literal(LiteralKind::Int(-12345)),
            TokenKind::Literal(LiteralKind::Float(123.456)),
            TokenKind::Literal(LiteralKind::Float(12345.67)),
            TokenKind::Literal(LiteralKind::Float(-123.456)),
            TokenKind::Literal(LiteralKind::Float(-12345.67)),
            TokenKind::Ident("my_ident".to_string()),
            TokenKind::Ident("my_2nd_ident".to_string()),
            TokenKind::TypeAnnotation(TypeAnnotationKind::String),
            TokenKind::Eof,
        ];

        let mut lexer = Lexer::new(input);
        let actual = lexer.lex().unwrap();

        for i in 0..expected.len() {
            assert_eq!(expected[i], actual[i].kind, "token was not as expected");
        }

        assert_eq!(
            expected.len(),
            actual.len(),
            "number of tokens does not match expected. expected {}, actual {}",
            expected.len(),
            actual.len(),
        );
    }

    #[test]
    fn scan_token_errors_on_unterminated_string() {
        let mut lexer = Lexer::new("\"this string is unterminated");
        let result = lexer.lex();

        match result {
            Err(LexerError::LexError {
                message,
                line: _,
                col: _,
            }) => {
                assert_eq!("unterminated string encountered".to_string(), message);
            }
            _ => panic!("expected LexError::LexError was not returned"),
        }
    }
}
