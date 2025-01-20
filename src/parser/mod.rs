use std::slice::Iter;

use crate::lexer::TokenType;
use anyhow::Context;
use anyhow::anyhow;

#[derive(Debug, PartialEq)]
pub enum Operator {
    Negation,
    BitwiseComplement,
    LogicalNegation
}

impl Operator {
    fn get_from_token(t: &TokenType) -> anyhow::Result<Self>{
        match t {
            TokenType::Minus => Ok(Self::Negation),
            TokenType::BitwiseComplement => Ok(Self::BitwiseComplement),
            TokenType::LogicalNegation => Ok(Self::LogicalNegation),
            _ => Err(anyhow!("Unsupported operator"))
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum AstNode {
    Program {
        function: Box<Self>,
    },
    Function {
        identifier: String,
        statement: Box<Self>,
    },
    Statement {
        expression: Box<Self>,
    },
    // Expressions
    UnaryOp {
        operator: Operator,
        expression: Box<Self>,
    },
    Constant {
        constant: u32,
    }
}

impl AstNode {
    pub fn parse(tokens: &[TokenType]) -> anyhow::Result<Self> {
        let mut token_iter = tokens.iter();
        let function: Self = Self::parse_function(&mut token_iter)?;
        Ok(Self::Program{ function: Box::new(function) })
    }

    fn parse_function(token_iter: &mut Iter<TokenType>) -> anyhow::Result<Self> {
        // parse keyword token
        if let TokenType::Keyword(s) = Self::get_next_token_from_iter(token_iter)? {
            if s != "int"  {
                return Err(anyhow!("First keyword of function is not 'int'"));
            }
        }
        else {
            return Err(anyhow!("First token of function is not a keyword"));
        }

        // Parse identifier
        let identifier: String;
        if let TokenType::Identifier(s) = Self::get_next_token_from_iter(token_iter)? {
            identifier = s.to_string();
        } else {
            return Err(anyhow!("No function identifier found"));
        }

        // () after identifier
        let TokenType::OpenParens = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("No open parens"));
        };
        let TokenType::ClosedParens = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("No closed parens"));
        };

        // {
        let TokenType::OpenBrace = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("No open brace"));
        };
        // parse statement
        let statement = Self::parse_statement(token_iter)?;
        // }
        let TokenType::ClosedBrace = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("No closed brace"));
        }; 

        // return node
        Ok(Self::Function { identifier, statement: Box::new(statement) })

    }

    fn parse_statement(token_iter: &mut Iter<TokenType>) -> anyhow::Result<Self> {
        // parse keyword token
        if let TokenType::Keyword(s) = Self::get_next_token_from_iter(token_iter)? {
            if s != "return" {
                return Err(anyhow!("First keyword of statement is not 'return'"))
            }
        } else {
            return Err(anyhow!("First token of statement is not a keyword"));
        }

        let expression = Self::parse_expression(token_iter)?;
        let statement = Self::Statement{expression: Box::new(expression)};

        // must end in semicolon
        let TokenType::Semicolon = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("Statement does not end in semicolon"));
        };

        // return node
        Ok(statement)
    }

    fn parse_expression(token_iter: &mut Iter<TokenType>) -> anyhow::Result<Self> {
        let token = Self::get_next_token_from_iter(token_iter)?;
        match token {
            TokenType::IntLiteral(constant) => Ok(Self::Constant { constant: *constant }),
            TokenType::Minus | TokenType::BitwiseComplement | TokenType::LogicalNegation  => {
                let nested_expression = Self::parse_expression(token_iter)?;
                let operator = Operator::get_from_token(token)?;
                Ok(Self::UnaryOp { operator, expression: Box::new(nested_expression)})
            },
            _ => Err(anyhow!("Could not parse expression"))
        }
    }

    fn get_next_token_from_iter<'a>(token_iter: &mut Iter<'a, TokenType>) -> anyhow::Result<&'a TokenType>{
        token_iter.next().context(anyhow!("no next token"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_unary_op() {
        let token_vec = vec![TokenType::BitwiseComplement, TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter());
        assert_eq!(
            exp.unwrap(), 
            AstNode::UnaryOp { 
                operator: Operator::BitwiseComplement, 
                expression: Box::new(AstNode::Constant { constant: 2 }),
            }
        );
    }

    #[test]
    fn test_parse_unary_op_nested() {
        let token_vec = vec![TokenType::BitwiseComplement, TokenType::BitwiseComplement, TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter());
        assert_eq!(
            exp.unwrap(), 
            AstNode::UnaryOp { 
                operator: Operator::BitwiseComplement, 
                expression: Box::new(
                    AstNode::UnaryOp { 
                        operator: Operator::BitwiseComplement, 
                        expression: Box::new(
                            AstNode::Constant { constant: 2 }
                        ),
                    },
                ),
            }
        );
    }

    #[test]
    fn test_parse_constant() {
        let token_vec = vec![TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter());
        assert_eq!(exp.unwrap(), AstNode::Constant{constant: 2});
    }

    #[test]
    fn test_parse_statement() {
        let token_vec = vec![TokenType::Keyword("return".into()), TokenType::IntLiteral(2), TokenType::Semicolon];
        let statement: anyhow::Result<AstNode> = AstNode::parse_statement(&mut token_vec.iter());
        let expression = Box::new(AstNode::Constant { constant: 2 });
        assert_eq!(statement.unwrap(), AstNode::Statement{expression});
    }


    #[test]
    fn test_parse_function() {
        let token_vec = vec![
            TokenType::Keyword("int".into()),
            TokenType::Identifier("main".into()),
            TokenType::OpenParens,
            TokenType::ClosedParens,
            TokenType::OpenBrace,
            TokenType::Keyword("return".into()), 
            TokenType::IntLiteral(2), TokenType::Semicolon,
            TokenType::ClosedBrace
        ];
        let function: anyhow::Result<AstNode> = AstNode::parse_function(&mut token_vec.iter());
        let expression = Box::new(AstNode::Constant { constant: 2 });
        let statement = Box::new(AstNode::Statement {expression});
        assert_eq!(function.unwrap(), AstNode::Function { identifier: "main".into(), statement });
    }
}