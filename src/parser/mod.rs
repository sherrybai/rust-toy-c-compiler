use std::{slice::Iter, string};

use crate::lexer::TokenType;
use anyhow::{Context};
use anyhow::anyhow;

#[derive(Debug, PartialEq)]
pub enum AstNode {
    Program,
    Function,
    Statement {
        expression: Box<AstNode>,
    },
    Expression {
        constant: u64,
    }
}



impl AstNode {
    pub fn parse(tokens: &[TokenType]) {
        // pass
    }

    fn parse_statement(token_iter: &mut Iter<TokenType>) -> anyhow::Result<Self> {
        let token = token_iter.next().context(anyhow!("no next token"))?;

        match token {
            TokenType::Keyword(s) => {
                if s != "return" {
                    return Err(anyhow!("Keyword is not 'return'"))
                }
                let expression = AstNode::parse_expression(token_iter)?;
                Ok(AstNode::Statement{expression: Box::new(expression)})
            },
            _ => Err(anyhow!("Keyword not found"))
        }
    }

    fn parse_expression(token_iter: &mut Iter<TokenType>) -> anyhow::Result<Self> {
        let token = token_iter.next().context(anyhow!("no next token"))?;
        match token {
            TokenType::IntLiteral(constant) => {
                Ok(AstNode::Expression{constant: *constant})
            },
            _ => Err(anyhow!("Expression not a constant"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_expression() {
        let mut token_vec = vec![TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter());
        assert_eq!(exp.unwrap(), AstNode::Expression{constant: 2});
    }
}