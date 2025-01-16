use std::slice::Iter;

use crate::lexer::TokenType;
use anyhow::Context;
use anyhow::anyhow;

#[derive(Debug, PartialEq)]
pub enum AstNode {
    Program {
        function: Box<AstNode>,
    },
    Function {
        identifier: String,
        statement: Box<AstNode>,
    },
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

    fn parse_function(token_iter: &mut Iter<TokenType>) -> anyhow::Result<Self> {
        // Parse keyword token
        if let TokenType::Keyword(s) = token_iter.next().context(anyhow!("no next token"))? {
            if s != "int"  {
                return Err(anyhow!("First keyword of function is not 'int'"));
            }
        }
        else {
            return Err(anyhow!("First token of function is not a keyword"));
        }

        // Parse identifier
        let identifier: String;
        if let TokenType::Identifier(s) = token_iter.next().context(anyhow!("no next token"))? {
            identifier = s.to_string();
        } else {
            return Err(anyhow!("No function identifier found"));
        }

        // () after identifier
        let TokenType::OpenParens = token_iter.next().context(anyhow!("no next token"))? else {
            return Err(anyhow!("No open parens"));
        };
        let TokenType::ClosedParens = token_iter.next().context(anyhow!("no next token"))? else {
            return Err(anyhow!("No closed parens"));
        };

        // {
        let TokenType::OpenBrace = token_iter.next().context(anyhow!("no next token"))? else {
            return Err(anyhow!("No open brace"));
        };
        // parse statement
        let statement = AstNode::parse_statement(token_iter)?;
        // }
        let TokenType::ClosedBrace = token_iter.next().context(anyhow!("no next token"))? else {
            return Err(anyhow!("No closed brace"));
        }; 

        // return node
        Ok(AstNode::Function { identifier, statement: Box::new(statement) })

    }

    fn parse_statement(token_iter: &mut Iter<TokenType>) -> anyhow::Result<Self> {
        let keyword_token = token_iter.next().context(anyhow!("no next token"))?;
        let statement: AstNode;
        match keyword_token {
            TokenType::Keyword(s) => {
                if s != "return" {
                    return Err(anyhow!("First keyword of statement is not 'return'"))
                }
                let expression = AstNode::parse_expression(token_iter)?;
                statement = AstNode::Statement{expression: Box::new(expression)};
            },
            _ => { return Err(anyhow!("First token of statement is not a keyword")) }
        }
        let semicolon_token = token_iter.next().context(anyhow!("no next token"))?;
        match semicolon_token {
            TokenType::Semicolon => Ok(statement),
            _ => Err(anyhow!("Statement does not end in semicolon"))
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
        let token_vec = vec![TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter());
        assert_eq!(exp.unwrap(), AstNode::Expression{constant: 2});
    }

    #[test]
    fn test_parse_statement() {
        let token_vec = vec![TokenType::Keyword("return".into()), TokenType::IntLiteral(2), TokenType::Semicolon];
        let statement: anyhow::Result<AstNode> = AstNode::parse_statement(&mut token_vec.iter());
        let expression = Box::new(AstNode::Expression { constant: 2 });
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
        let expression = Box::new(AstNode::Expression { constant: 2 });
        let statement = Box::new(AstNode::Statement {expression});
        assert_eq!(function.unwrap(), AstNode::Function { identifier: "main".into(), statement });
    }
}