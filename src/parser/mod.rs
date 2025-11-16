use crate::{
    lexer::token::{KeywordKind, LiteralKind, Token, TokenKind},
    parser::{
        ast::{
            Assign, Binary, BlockStmt, Call, Expr, ForStmt, Function, FunctionParam, Grouping,
            IfStmt, LetStmt, Literal, PrintStmt, ReturnStmt, Stmt, Unary, Variable,
        },
        errors::ParserError,
    },
};

pub mod ast;
pub mod errors;

pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, current: 0 }
    }

    pub fn parse(&mut self) -> Result<Vec<Stmt>, ParserError> {
        let mut declarations = Vec::new();

        while !self.is_at_end() {
            declarations.push(self.parse_declaration()?);
        }

        Ok(declarations)
    }

    fn parse_declaration(&mut self) -> Result<Stmt, ParserError> {
        if self.advance_if(&TokenKind::Keyword(KeywordKind::Function)) {
            return self.parse_fn_declaration();
        }
        if self.advance_if(&TokenKind::Keyword(KeywordKind::Let)) {
            return self.parse_let_declaration();
        }

        self.parse_statement()
    }

    fn parse_fn_declaration(&mut self) -> Result<Stmt, ParserError> {
        if !matches!(self.peek().kind, TokenKind::Ident(_)) {
            return Err(self.report_parse_error("expected function name"));
        }

        let name = self.advance().clone();

        if !self.advance_if(&TokenKind::LeftParen) {
            return Err(self.report_parse_error("expected ( after function identifier"));
        }

        let mut parameters = Vec::new();
        if self.peek().kind != TokenKind::RightParen {
            loop {
                if matches!(self.peek().kind, TokenKind::Ident(_)) {
                    let name = self.advance().clone();

                    if !self.advance_if(&TokenKind::Colon) {
                        return Err(self.report_parse_error("expected type annotation"));
                    }

                    let next_token = self.peek().clone();
                    if let TokenKind::TypeAnnotation(_) = next_token.kind {
                        self.advance();
                        parameters.push(FunctionParam::new(name, next_token))
                    } else {
                        return Err(self.report_parse_error("expected type annotation"));
                    }
                }

                if !self.advance_if(&TokenKind::Comma) {
                    break;
                }
            }
        }

        if !self.advance_if(&TokenKind::RightParen) {
            return Err(self.report_parse_error("expected closing ) after function params"));
        }

        let mut return_type = None;
        if self.advance_if(&TokenKind::Colon) {
            if let TokenKind::TypeAnnotation(_) = self.peek().kind {
                return_type = Some(self.advance().clone());
            }
        }

        if !self.advance_if(&TokenKind::LeftBrace) {
            return Err(self
                .report_parse_error("expected { or return type annotation before function body"));
        }

        let body = self.parse_block_statements()?;

        Ok(Stmt::Expression(Expr::Function(Function::new(
            name,
            parameters,
            return_type,
            body,
        ))))
    }

    fn parse_let_declaration(&mut self) -> Result<Stmt, ParserError> {
        let ident = self.peek().clone();

        if !self.advance_if_predicate(|token_kind| matches!(token_kind, &TokenKind::Ident(_))) {
            return Err(self.report_parse_error("expected variable identifier"));
        }

        let mut type_annotation = None;
        if self.advance_if(&TokenKind::Colon) {
            if let TokenKind::TypeAnnotation(_) = self.peek().kind {
                type_annotation = Some(self.advance().clone());
            }
        }

        let mut initialiser: Option<Expr> = None;
        if self.advance_if(&TokenKind::Equal) {
            let expr = self.parse_expression()?;
            initialiser = Some(expr);
        }

        if !self.advance_if(&TokenKind::Semicolon) {
            return Err(self.report_parse_error("expected ; after let declaration"));
        }

        Ok(Stmt::Let(LetStmt::new(ident, type_annotation, initialiser)))
    }

    fn parse_statement(&mut self) -> Result<Stmt, ParserError> {
        match self.peek().kind {
            TokenKind::Keyword(KeywordKind::For) => {
                self.advance();

                self.parse_for_statement()
            }
            TokenKind::Keyword(KeywordKind::If) => {
                self.advance();

                self.parse_if_statement()
            }
            TokenKind::LeftBrace => {
                self.advance();

                let block_statements = self.parse_block_statements()?;

                Ok(Stmt::Block(BlockStmt::new(block_statements)))
            }
            TokenKind::Keyword(KeywordKind::Print) => {
                self.advance();

                self.parse_print_stmt()
            }
            TokenKind::Keyword(KeywordKind::Return) => {
                self.advance();

                self.parse_return_stmt()
            }
            _ => self.parse_expression_statement(),
        }
    }

    fn parse_for_statement(&mut self) -> Result<Stmt, ParserError> {
        let condition = self.parse_expression()?;
        let body = self.parse_statement()?;

        Ok(Stmt::For(ForStmt::new(condition, body)))
    }

    fn parse_if_statement(&mut self) -> Result<Stmt, ParserError> {
        let condition = self.parse_expression()?;

        let then_branch = self.parse_statement()?;
        let mut else_branch: Option<Stmt> = None;

        if self.advance_if(&TokenKind::Keyword(KeywordKind::Else)) {
            else_branch = Some(self.parse_statement()?);
        }

        Ok(Stmt::If(IfStmt::new(condition, then_branch, else_branch)))
    }

    fn parse_print_stmt(&mut self) -> Result<Stmt, ParserError> {
        let expr = self.parse_expression()?;

        if !self.advance_if(&TokenKind::Semicolon) {
            return Err(self.report_parse_error("expected ; after statement"));
        }

        Ok(Stmt::Print(PrintStmt::new(expr)))
    }

    fn parse_return_stmt(&mut self) -> Result<Stmt, ParserError> {
        let mut value: Option<Expr> = None;

        if self.peek().kind != TokenKind::Semicolon {
            value = Some(self.parse_expression()?)
        }

        if !self.advance_if(&TokenKind::Semicolon) {
            return Err(self.report_parse_error("expected ; after return statement"));
        }

        Ok(Stmt::Return(ReturnStmt::new(value)))
    }

    fn parse_block_statements(&mut self) -> Result<Vec<Stmt>, ParserError> {
        let mut statements: Vec<Stmt> = Vec::new();

        loop {
            if self.is_at_end() || self.peek().kind == TokenKind::RightBrace {
                break;
            }

            statements.push(self.parse_declaration()?);
        }

        if !self.advance_if(&TokenKind::RightBrace) {
            return Err(self.report_parse_error("unterminated block statement encountered"));
        }

        Ok(statements)
    }

    fn parse_expression_statement(&mut self) -> Result<Stmt, ParserError> {
        let expr = self.parse_expression()?;

        if !self.advance_if(&TokenKind::Semicolon) {
            return Err(self.report_parse_error("expected ; after statement"));
        }

        Ok(Stmt::Expression(expr))
    }

    fn parse_expression(&mut self) -> Result<Expr, ParserError> {
        self.parse_assignment()
    }

    fn parse_assignment(&mut self) -> Result<Expr, ParserError> {
        let expr = self.parse_equality()?;

        if self.advance_if(&TokenKind::Equal) {
            let value = self.parse_assignment()?;

            if let Expr::Variable(variable) = expr {
                let Variable { name } = variable;

                return Ok(Expr::Assign(Assign::new(name, value)));
            }

            return Err(self.report_parse_error("invalid assignment target"));
        }

        Ok(expr)
    }

    fn parse_equality(&mut self) -> Result<Expr, ParserError> {
        let expr = self.parse_comparison()?;

        if let TokenKind::BangEqual | TokenKind::EqualEqual = self.peek().kind {
            self.advance();

            let operator = self.previous().clone();
            let right = self.parse_comparison()?;

            return Ok(Expr::Binary(Binary::new(expr, operator, right)));
        }

        Ok(expr)
    }

    fn parse_comparison(&mut self) -> Result<Expr, ParserError> {
        let expr = self.parse_term()?;

        match self.peek().kind {
            TokenKind::Greater
            | TokenKind::GreaterEqual
            | TokenKind::Less
            | TokenKind::LessEqual => {
                self.advance();

                let operator = self.previous().clone();
                let right = self.parse_term()?;

                Ok(Expr::Binary(Binary::new(expr, operator, right)))
            }
            _ => Ok(expr),
        }
    }

    fn parse_term(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_factor()?;

        while matches!(self.peek().kind, TokenKind::Plus | TokenKind::Minus) {
            self.advance();

            let operator = self.previous().clone();
            let right = self.parse_factor()?;

            expr = Expr::Binary(Binary::new(expr, operator, right))
        }

        Ok(expr)
    }

    fn parse_factor(&mut self) -> Result<Expr, ParserError> {
        let expr = self.parse_unary()?;
        let next_token = self.peek();

        if let TokenKind::Slash | TokenKind::Asterisk = next_token.kind {
            self.advance();

            let operator = self.previous().clone();
            let right = self.parse_unary()?;

            return Ok(Expr::Binary(Binary::new(expr, operator, right)));
        }

        Ok(expr)
    }

    fn parse_unary(&mut self) -> Result<Expr, ParserError> {
        let next_token = self.peek();

        if let TokenKind::Bang | TokenKind::Minus = next_token.kind {
            self.advance();

            let operator = self.previous().clone();
            let right = self.parse_unary()?;

            return Ok(Expr::Unary(Unary::new(operator, right)));
        }

        self.parse_fn_call()
    }

    fn parse_fn_call(&mut self) -> Result<Expr, ParserError> {
        let mut expr = self.parse_primary()?;

        loop {
            if self.advance_if(&TokenKind::LeftParen) {
                expr = self.parse_end_fn_call(expr)?;
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_end_fn_call(&mut self, callee: Expr) -> Result<Expr, ParserError> {
        let mut arguments = Vec::new();

        if self.peek().kind != TokenKind::RightParen {
            loop {
                arguments.push(self.parse_expression()?);

                if !self.advance_if(&TokenKind::Comma) {
                    break;
                }
            }
        }

        if !self.advance_if(&TokenKind::RightParen) {
            return Err(self.report_parse_error("expected closing ) after function args"));
        }

        Ok(Expr::Call(Call::new(callee, arguments)))
    }

    fn parse_primary(&mut self) -> Result<Expr, ParserError> {
        let next_token = self.advance();

        match &next_token.kind {
            TokenKind::Literal(literal) => match literal {
                LiteralKind::Boolean(value) => Ok(Expr::Literal(Literal::Boolean(*value))),
                LiteralKind::Int(value) => Ok(Expr::Literal(Literal::Int(*value))),
                LiteralKind::Float(value) => Ok(Expr::Literal(Literal::Float(*value))),
                LiteralKind::String(value) => Ok(Expr::Literal(Literal::String(value.to_string()))),
            },
            TokenKind::LeftParen => {
                let expr = self.parse_expression()?;

                if !self.advance_if(&TokenKind::RightParen) {
                    return Err(self.report_parse_error("expected closing )"));
                }

                Ok(Expr::Grouping(Grouping::new(expr)))
            }
            TokenKind::Ident(_) => Ok(Expr::Variable(Variable::new(next_token.clone()))),

            _ => {
                println!("{:#?}", next_token.kind);
                Err(self.report_parse_error("expected expression"))
            }
        }
    }

    fn advance(&mut self) -> &Token {
        let token = &self.tokens[self.current];

        self.current += 1;
        token
    }

    fn advance_if(&mut self, token_kind: &TokenKind) -> bool {
        self.advance_if_predicate(|kind| kind == token_kind)
    }

    fn advance_if_predicate<F>(&mut self, predicate: F) -> bool
    where
        F: Fn(&TokenKind) -> bool,
    {
        if predicate(&self.peek().kind) {
            self.advance();
            return true;
        }

        false
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.current]
    }

    fn previous(&self) -> &Token {
        &self.tokens[self.current - 1]
    }

    fn is_at_end(&self) -> bool {
        self.peek().kind == TokenKind::Eof
    }

    fn report_parse_error(&self, message: &str) -> ParserError {
        let problem_token = self.previous();

        ParserError::ParseError {
            message: message.to_string(),
            line: problem_token.line,
            col: problem_token.col,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::token::TypeAnnotationKind;

    use super::*;

    fn token(kind: TokenKind) -> Token {
        Token::new(kind, 1, 1)
    }

    #[test]
    fn let_declaration_without_assignment_is_parsed() {
        let tokens = vec![
            token(TokenKind::Keyword(KeywordKind::Let)),
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::Semicolon),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::Let(LetStmt::new(
            token(TokenKind::Ident("foo".to_string())),
            None,
            None,
        ))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn type_annotated_let_declaration_without_assignment_is_parsed() {
        let tokens = vec![
            token(TokenKind::Keyword(KeywordKind::Let)),
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::Colon),
            token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int)),
            token(TokenKind::Semicolon),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::Let(LetStmt::new(
            token(TokenKind::Ident("foo".to_string())),
            Some(token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int))),
            None,
        ))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn let_declaration_with_assignment_is_parsed() {
        let tokens = vec![
            token(TokenKind::Keyword(KeywordKind::Let)),
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Literal(LiteralKind::String("bar".to_string()))),
            token(TokenKind::Semicolon),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::Let(LetStmt::new(
            token(TokenKind::Ident("foo".to_string())),
            None,
            Some(Expr::Literal(Literal::String("bar".to_string()))),
        ))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn type_annotated_let_declaration_with_assignment_is_parsed() {
        let tokens = vec![
            token(TokenKind::Keyword(KeywordKind::Let)),
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::Colon),
            token(TokenKind::TypeAnnotation(TypeAnnotationKind::String)),
            token(TokenKind::Equal),
            token(TokenKind::Literal(LiteralKind::String("bar".to_string()))),
            token(TokenKind::Semicolon),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::Let(LetStmt::new(
            token(TokenKind::Ident("foo".to_string())),
            Some(token(TokenKind::TypeAnnotation(TypeAnnotationKind::String))),
            Some(Expr::Literal(Literal::String("bar".to_string()))),
        ))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn assignment_is_parsed() {
        let tokens = vec![
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Literal(LiteralKind::String("bar".to_string()))),
            token(TokenKind::Semicolon),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::Expression(Expr::Assign(Assign::new(
            token(TokenKind::Ident("foo".to_string())),
            Expr::Literal(Literal::String("bar".to_string())),
        )))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn for_statement_is_parsed() {
        let tokens = vec![
            token(TokenKind::Keyword(KeywordKind::For)),
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::LessEqual),
            token(TokenKind::Literal(LiteralKind::Int(5))),
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Plus),
            token(TokenKind::Literal(LiteralKind::Int(1))),
            token(TokenKind::Semicolon),
            token(TokenKind::RightBrace),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::For(ForStmt::new(
            Expr::Binary(Binary::new(
                Expr::Variable(Variable::new(token(TokenKind::Ident("foo".to_string())))),
                token(TokenKind::LessEqual),
                Expr::Literal(Literal::Int(5)),
            )),
            Stmt::Block(BlockStmt::new(vec![Stmt::Expression(Expr::Assign(
                Assign::new(
                    token(TokenKind::Ident("a".to_string())),
                    Expr::Binary(Binary::new(
                        Expr::Variable(Variable::new(token(TokenKind::Ident("a".to_string())))),
                        token(TokenKind::Plus),
                        Expr::Literal(Literal::Int(1)),
                    )),
                ),
            ))])),
        ))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn if_statement_is_parsed() {
        let tokens = vec![
            token(TokenKind::Keyword(KeywordKind::If)),
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::GreaterEqual),
            token(TokenKind::Literal(LiteralKind::Int(-5))),
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Plus),
            token(TokenKind::Literal(LiteralKind::Int(1))),
            token(TokenKind::Semicolon),
            token(TokenKind::RightBrace),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::If(IfStmt::new(
            Expr::Binary(Binary::new(
                Expr::Variable(Variable::new(token(TokenKind::Ident("foo".to_string())))),
                token(TokenKind::GreaterEqual),
                Expr::Literal(Literal::Int(-5)),
            )),
            Stmt::Block(BlockStmt::new(vec![Stmt::Expression(Expr::Assign(
                Assign::new(
                    token(TokenKind::Ident("a".to_string())),
                    Expr::Binary(Binary::new(
                        Expr::Variable(Variable::new(token(TokenKind::Ident("a".to_string())))),
                        token(TokenKind::Plus),
                        Expr::Literal(Literal::Int(1)),
                    )),
                ),
            ))])),
            None,
        ))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn if_else_statement_is_parsed() {
        let tokens = vec![
            token(TokenKind::Keyword(KeywordKind::If)),
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::GreaterEqual),
            token(TokenKind::Literal(LiteralKind::Int(-5))),
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Plus),
            token(TokenKind::Literal(LiteralKind::Int(1))),
            token(TokenKind::Semicolon),
            token(TokenKind::RightBrace),
            token(TokenKind::Keyword(KeywordKind::Else)),
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("b".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("b".to_string())),
            token(TokenKind::Minus),
            token(TokenKind::Literal(LiteralKind::Int(2))),
            token(TokenKind::Semicolon),
            token(TokenKind::RightBrace),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::If(IfStmt::new(
            Expr::Binary(Binary::new(
                Expr::Variable(Variable::new(token(TokenKind::Ident("foo".to_string())))),
                token(TokenKind::GreaterEqual),
                Expr::Literal(Literal::Int(-5)),
            )),
            Stmt::Block(BlockStmt::new(vec![Stmt::Expression(Expr::Assign(
                Assign::new(
                    token(TokenKind::Ident("a".to_string())),
                    Expr::Binary(Binary::new(
                        Expr::Variable(Variable::new(token(TokenKind::Ident("a".to_string())))),
                        token(TokenKind::Plus),
                        Expr::Literal(Literal::Int(1)),
                    )),
                ),
            ))])),
            Some(Stmt::Block(BlockStmt::new(vec![Stmt::Expression(
                Expr::Assign(Assign::new(
                    token(TokenKind::Ident("b".to_string())),
                    Expr::Binary(Binary::new(
                        Expr::Variable(Variable::new(token(TokenKind::Ident("b".to_string())))),
                        token(TokenKind::Minus),
                        Expr::Literal(Literal::Int(2)),
                    )),
                )),
            )]))),
        ))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn if_else_if_else_statement_is_parsed() {
        let tokens = vec![
            token(TokenKind::Keyword(KeywordKind::If)),
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::GreaterEqual),
            token(TokenKind::Literal(LiteralKind::Int(-5))),
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Plus),
            token(TokenKind::Literal(LiteralKind::Int(1))),
            token(TokenKind::Semicolon),
            token(TokenKind::RightBrace),
            token(TokenKind::Keyword(KeywordKind::Else)),
            token(TokenKind::Keyword(KeywordKind::If)),
            token(TokenKind::Ident("bar".to_string())),
            token(TokenKind::Less),
            token(TokenKind::Literal(LiteralKind::Int(10))),
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("b".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("b".to_string())),
            token(TokenKind::Slash),
            token(TokenKind::Literal(LiteralKind::Int(2))),
            token(TokenKind::Semicolon),
            token(TokenKind::RightBrace),
            token(TokenKind::Keyword(KeywordKind::Else)),
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("c".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("c".to_string())),
            token(TokenKind::Asterisk),
            token(TokenKind::Literal(LiteralKind::Int(7))),
            token(TokenKind::Semicolon),
            token(TokenKind::RightBrace),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::If(IfStmt::new(
            Expr::Binary(Binary::new(
                Expr::Variable(Variable::new(token(TokenKind::Ident("foo".to_string())))),
                token(TokenKind::GreaterEqual),
                Expr::Literal(Literal::Int(-5)),
            )),
            Stmt::Block(BlockStmt::new(vec![Stmt::Expression(Expr::Assign(
                Assign::new(
                    token(TokenKind::Ident("a".to_string())),
                    Expr::Binary(Binary::new(
                        Expr::Variable(Variable::new(token(TokenKind::Ident("a".to_string())))),
                        token(TokenKind::Plus),
                        Expr::Literal(Literal::Int(1)),
                    )),
                ),
            ))])),
            Some(Stmt::If(IfStmt::new(
                Expr::Binary(Binary::new(
                    Expr::Variable(Variable::new(token(TokenKind::Ident("bar".to_string())))),
                    token(TokenKind::Less),
                    Expr::Literal(Literal::Int(10)),
                )),
                Stmt::Block(BlockStmt::new(vec![Stmt::Expression(Expr::Assign(
                    Assign::new(
                        token(TokenKind::Ident("b".to_string())),
                        Expr::Binary(Binary::new(
                            Expr::Variable(Variable::new(token(TokenKind::Ident("b".to_string())))),
                            token(TokenKind::Slash),
                            Expr::Literal(Literal::Int(2)),
                        )),
                    ),
                ))])),
                Some(Stmt::Block(BlockStmt::new(vec![Stmt::Expression(
                    Expr::Assign(Assign::new(
                        token(TokenKind::Ident("c".to_string())),
                        Expr::Binary(Binary::new(
                            Expr::Variable(Variable::new(token(TokenKind::Ident("c".to_string())))),
                            token(TokenKind::Asterisk),
                            Expr::Literal(Literal::Int(7)),
                        )),
                    )),
                )]))),
            ))),
        ))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn block_statement_is_parsed() {
        let tokens = vec![
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Plus),
            token(TokenKind::Literal(LiteralKind::Int(1))),
            token(TokenKind::Semicolon),
            token(TokenKind::RightBrace),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::Block(BlockStmt::new(vec![Stmt::Expression(
            Expr::Assign(Assign::new(
                token(TokenKind::Ident("a".to_string())),
                Expr::Binary(Binary::new(
                    Expr::Variable(Variable::new(token(TokenKind::Ident("a".to_string())))),
                    token(TokenKind::Plus),
                    Expr::Literal(Literal::Int(1)),
                )),
            )),
        )]))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn block_statement_errors_on_unterminated_block() {
        let tokens = vec![
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Plus),
            token(TokenKind::Literal(LiteralKind::Int(1))),
            token(TokenKind::Semicolon),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();

        match result {
            Err(ParserError::ParseError {
                message,
                line: 1,
                col: 1,
            }) => {
                assert_eq!(
                    "unterminated block statement encountered".to_string(),
                    message
                );
            }
            _ => panic!("expected ParseError::ParseError was not returned"),
        }
    }

    #[test]
    fn function_calls_without_arguments_are_parsed() {
        let tokens = vec![
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::LeftParen),
            token(TokenKind::RightParen),
            token(TokenKind::Semicolon),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let actual = parser.parse().unwrap();

        let expected = vec![Stmt::Expression(Expr::Call(Call::new(
            Expr::Variable(Variable::new(token(TokenKind::Ident("foo".to_string())))),
            Vec::new(),
        )))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn function_calls_with_arguments_are_parsed() {
        let tokens = vec![
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::LeftParen),
            token(TokenKind::Ident("bar".to_string())),
            token(TokenKind::Comma),
            token(TokenKind::Ident("baz".to_string())),
            token(TokenKind::RightParen),
            token(TokenKind::Semicolon),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let actual = parser.parse().unwrap();

        let expected = vec![Stmt::Expression(Expr::Call(Call::new(
            Expr::Variable(Variable::new(token(TokenKind::Ident("foo".to_string())))),
            vec![
                Expr::Variable(Variable::new(token(TokenKind::Ident("bar".to_string())))),
                Expr::Variable(Variable::new(token(TokenKind::Ident("baz".to_string())))),
            ],
        )))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn functions_without_parameters_are_parsed() {
        let tokens = vec![
            token(TokenKind::Keyword(KeywordKind::Function)),
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::LeftParen),
            token(TokenKind::RightParen),
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Plus),
            token(TokenKind::Literal(LiteralKind::Int(1))),
            token(TokenKind::Semicolon),
            token(TokenKind::RightBrace),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::Expression(Expr::Function(Function::new(
            token(TokenKind::Ident("foo".to_string())),
            Vec::new(),
            None,
            vec![Stmt::Expression(Expr::Assign(Assign::new(
                token(TokenKind::Ident("a".to_string())),
                Expr::Binary(Binary::new(
                    Expr::Variable(Variable::new(token(TokenKind::Ident("a".to_string())))),
                    token(TokenKind::Plus),
                    Expr::Literal(Literal::Int(1)),
                )),
            )))],
        )))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn functions_with_parameters_are_parsed() {
        let tokens = vec![
            token(TokenKind::Keyword(KeywordKind::Function)),
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::LeftParen),
            token(TokenKind::Ident("bar".to_string())),
            token(TokenKind::Colon),
            token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int)),
            token(TokenKind::Comma),
            token(TokenKind::Ident("baz".to_string())),
            token(TokenKind::Colon),
            token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int)),
            token(TokenKind::RightParen),
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Plus),
            token(TokenKind::Literal(LiteralKind::Int(1))),
            token(TokenKind::Semicolon),
            token(TokenKind::RightBrace),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::Expression(Expr::Function(Function::new(
            token(TokenKind::Ident("foo".to_string())),
            vec![
                FunctionParam::new(
                    token(TokenKind::Ident("bar".to_string())),
                    token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int)),
                ),
                FunctionParam::new(
                    token(TokenKind::Ident("baz".to_string())),
                    token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int)),
                ),
            ],
            None,
            vec![Stmt::Expression(Expr::Assign(Assign::new(
                token(TokenKind::Ident("a".to_string())),
                Expr::Binary(Binary::new(
                    Expr::Variable(Variable::new(token(TokenKind::Ident("a".to_string())))),
                    token(TokenKind::Plus),
                    Expr::Literal(Literal::Int(1)),
                )),
            )))],
        )))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn functions_with_return_types_are_parsed() {
        let tokens = vec![
            token(TokenKind::Keyword(KeywordKind::Function)),
            token(TokenKind::Ident("foo".to_string())),
            token(TokenKind::LeftParen),
            token(TokenKind::Ident("bar".to_string())),
            token(TokenKind::Colon),
            token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int)),
            token(TokenKind::Comma),
            token(TokenKind::Ident("baz".to_string())),
            token(TokenKind::Colon),
            token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int)),
            token(TokenKind::RightParen),
            token(TokenKind::Colon),
            token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int)),
            token(TokenKind::LeftBrace),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Equal),
            token(TokenKind::Ident("a".to_string())),
            token(TokenKind::Plus),
            token(TokenKind::Literal(LiteralKind::Int(1))),
            token(TokenKind::Semicolon),
            token(TokenKind::RightBrace),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::Expression(Expr::Function(Function::new(
            token(TokenKind::Ident("foo".to_string())),
            vec![
                FunctionParam::new(
                    token(TokenKind::Ident("bar".to_string())),
                    token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int)),
                ),
                FunctionParam::new(
                    token(TokenKind::Ident("baz".to_string())),
                    token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int)),
                ),
            ],
            Some(token(TokenKind::TypeAnnotation(TypeAnnotationKind::Int))),
            vec![Stmt::Expression(Expr::Assign(Assign::new(
                token(TokenKind::Ident("a".to_string())),
                Expr::Binary(Binary::new(
                    Expr::Variable(Variable::new(token(TokenKind::Ident("a".to_string())))),
                    token(TokenKind::Plus),
                    Expr::Literal(Literal::Int(1)),
                )),
            )))],
        )))];

        assert_eq!(expected, actual);
    }

    #[test]
    fn equality_operators_are_parsed() {
        let cases = vec![TokenKind::EqualEqual, TokenKind::BangEqual];

        for kind in cases {
            let tokens = vec![
                token(TokenKind::Literal(LiteralKind::Int(5))),
                token(kind.clone()),
                token(TokenKind::Literal(LiteralKind::Int(9))),
                token(TokenKind::Semicolon),
                token(TokenKind::Eof),
            ];

            let mut parser = Parser::new(tokens);
            let result = parser.parse();
            let actual = result.unwrap();

            let expected = vec![Stmt::Expression(Expr::Binary(Binary::new(
                Expr::Literal(Literal::Int(5)),
                token(kind),
                Expr::Literal(Literal::Int(9)),
            )))];

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn operator_expressions_are_parsed() {
        let cases = vec![
            TokenKind::Greater,
            TokenKind::GreaterEqual,
            TokenKind::Less,
            TokenKind::LessEqual,
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Slash,
            TokenKind::Asterisk,
        ];

        for kind in cases {
            let tokens = vec![
                token(TokenKind::Literal(LiteralKind::Int(5))),
                token(kind.clone()),
                token(TokenKind::Literal(LiteralKind::Int(9))),
                token(TokenKind::Semicolon),
                token(TokenKind::Eof),
            ];

            let mut parser = Parser::new(tokens);
            let result = parser.parse();
            let actual = result.unwrap();

            let expected = vec![Stmt::Expression(Expr::Binary(Binary::new(
                Expr::Literal(Literal::Int(5)),
                token(kind),
                Expr::Literal(Literal::Int(9)),
            )))];

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn unary_expressions_are_parsed() {
        let cases = vec![TokenKind::Bang, TokenKind::Minus];

        for kind in cases {
            let tokens = vec![
                token(kind.clone()),
                token(TokenKind::Literal(LiteralKind::Int(5))),
                token(TokenKind::Semicolon),
                token(TokenKind::Eof),
            ];

            let mut parser = Parser::new(tokens);
            let result = parser.parse();
            let actual = result.unwrap();

            let expected = vec![Stmt::Expression(Expr::Unary(Unary::new(
                token(kind),
                Expr::Literal(Literal::Int(5)),
            )))];

            assert_eq!(expected, actual);
        }
    }

    #[test]
    fn primary_literals_are_parsed() {
        let cases = vec![
            (
                token(TokenKind::Literal(LiteralKind::Boolean(true))),
                Stmt::Expression(Expr::Literal(Literal::Boolean(true))),
            ),
            (
                token(TokenKind::Literal(LiteralKind::Boolean(false))),
                Stmt::Expression(Expr::Literal(Literal::Boolean(false))),
            ),
            (
                token(TokenKind::Literal(LiteralKind::Int(-5))),
                Stmt::Expression(Expr::Literal(Literal::Int(-5))),
            ),
            (
                token(TokenKind::Literal(LiteralKind::Int(5))),
                Stmt::Expression(Expr::Literal(Literal::Int(5))),
            ),
            (
                token(TokenKind::Literal(LiteralKind::Float(5.1))),
                Stmt::Expression(Expr::Literal(Literal::Float(5.1))),
            ),
            (
                token(TokenKind::Literal(LiteralKind::String("hello".to_string()))),
                Stmt::Expression(Expr::Literal(Literal::String("hello".to_string()))),
            ),
        ];

        for (tok, expected_stmt) in cases {
            let tokens = vec![tok, token(TokenKind::Semicolon), token(TokenKind::Eof)];

            let mut parser = Parser::new(tokens);
            let result = parser.parse();
            let actual = result.unwrap();

            let expected = vec![expected_stmt];

            assert_eq!(expected, actual);
        }
    }

    #[test]
    pub fn primary_grouping_is_parsed() {
        let tokens = vec![
            token(TokenKind::LeftParen),
            token(TokenKind::Literal(LiteralKind::Int(5))),
            token(TokenKind::Asterisk),
            token(TokenKind::Literal(LiteralKind::Int(5))),
            token(TokenKind::RightParen),
            token(TokenKind::Plus),
            token(TokenKind::LeftParen),
            token(TokenKind::LeftParen),
            token(TokenKind::Literal(LiteralKind::Int(5))),
            token(TokenKind::Asterisk),
            token(TokenKind::Literal(LiteralKind::Int(5))),
            token(TokenKind::RightParen),
            token(TokenKind::Asterisk),
            token(TokenKind::Literal(LiteralKind::Int(3))),
            token(TokenKind::RightParen),
            token(TokenKind::Semicolon),
            token(TokenKind::Eof),
        ];

        let mut parser = Parser::new(tokens);
        let result = parser.parse();
        let actual = result.unwrap();

        let expected = vec![Stmt::Expression(Expr::Binary(Binary::new(
            Expr::Grouping(Grouping::new(Expr::Binary(Binary::new(
                Expr::Literal(Literal::Int(5)),
                token(TokenKind::Asterisk),
                Expr::Literal(Literal::Int(5)),
            )))),
            token(TokenKind::Plus),
            Expr::Grouping(Grouping::new(Expr::Binary(Binary::new(
                Expr::Grouping(Grouping::new(Expr::Binary(Binary::new(
                    Expr::Literal(Literal::Int(5)),
                    token(TokenKind::Asterisk),
                    Expr::Literal(Literal::Int(5)),
                )))),
                token(TokenKind::Asterisk),
                Expr::Literal(Literal::Int(3)),
            )))),
        )))];

        assert_eq!(expected, actual);
    }
}
