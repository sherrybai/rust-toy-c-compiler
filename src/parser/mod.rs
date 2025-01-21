use std::iter::Peekable;
use std::slice::Iter;

use crate::lexer::TokenType;
use anyhow::Context;
use anyhow::anyhow;

#[derive(Debug, PartialEq)]
pub enum Operator {
    Negation,
    BitwiseComplement,
    LogicalNegation,
    Subtraction,
    Addition,
    Multiplication,
    Division
}

impl Operator {
    fn get_unary_op_from_token(t: &TokenType) -> anyhow::Result<Self> {
        match t {
            TokenType::Minus => Ok(Self::Negation),
            TokenType::BitwiseComplement => Ok(Self::BitwiseComplement),
            TokenType::LogicalNegation => Ok(Self::LogicalNegation),
            _ => Err(anyhow!("Unsupported operator"))
        }
    }

    fn get_binary_op_from_token(t: &TokenType) -> anyhow::Result<Self> {
        match t {
            TokenType::Minus => Ok(Self::Subtraction),
            TokenType::Addition => Ok(Self::Addition),
            TokenType::Multiplication => Ok(Self::Multiplication),
            TokenType::Division => Ok(Self::Division),
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
    BinaryOp {
        operator: Operator,
        term: Box<Self>,      
        next_term: Box<Self>,
    },
    UnaryOp {
        operator: Operator,
        factor: Box<Self>,
    },
    Constant {
        constant: u32,
    }
}

impl AstNode {
    pub fn parse(tokens: &[TokenType]) -> anyhow::Result<Self> {
        let mut token_iter = tokens.iter().peekable();
        let function: Self = Self::parse_function(&mut token_iter)?;
        Ok(Self::Program{ function: Box::new(function) })
    }

    fn parse_function(token_iter: &mut Peekable<Iter<TokenType>>) -> anyhow::Result<Self> {
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

    fn parse_statement(token_iter: &mut Peekable<Iter<TokenType>>) -> anyhow::Result<Self> {
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

    fn parse_expression(token_iter: &mut Peekable<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <exp> ::= <term> { ("+" | "-") <term> }

        let mut term = Self::parse_term(token_iter)?;

        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(TokenType::Addition | TokenType::Minus) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_term = Self::parse_term(token_iter)?;
            term = AstNode::BinaryOp{ 
                operator: Operator::get_binary_op_from_token(token)?, 
                term: Box::new(term), 
                next_term: Box::new(next_term)
            };

            next_token = token_iter.peek();
        }

        Ok(term)
    }
    
    fn parse_term(token_iter: &mut Peekable<Iter<TokenType>>) -> anyhow::Result<Self> {
        // term: operand of addition/subtraction
        // <term> ::= <factor> { ("*" | "/") <factor> }

        let mut factor = Self::parse_factor(token_iter)?;

        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(TokenType::Multiplication | TokenType::Division) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_factor = Self::parse_factor(token_iter)?;
            factor = AstNode::BinaryOp{ 
                operator: Operator::get_binary_op_from_token(token)?, 
                term: Box::new(factor),
                next_term: Box::new(next_factor),
            };

            next_token = token_iter.peek();
        }

        Ok(factor)
    }

    fn parse_factor(token_iter: &mut Peekable<Iter<TokenType>>) -> anyhow::Result<Self> {
        // factor: operand of multiplication/division
        // <factor> ::= "(" <exp> ")" | <unary_op> <factor> | <int>

        let token = Self::get_next_token_from_iter(token_iter)?;

        match token {
            TokenType::OpenParens => {
                let expression = Self::parse_expression(token_iter)?;
                let closed_parens = Self::get_next_token_from_iter(token_iter)?;
                let TokenType::ClosedParens = closed_parens else {
                    return Err(anyhow!("Missing closed parentheses"))
                };
                Ok(expression)
            }
            TokenType::IntLiteral(constant) => Ok(Self::Constant { constant: *constant }),
            TokenType::Minus | TokenType::BitwiseComplement | TokenType::LogicalNegation  => {
                let nested_expression = Self::parse_factor(token_iter)?;
                let operator = Operator::get_unary_op_from_token(token)?;
                Ok(Self::UnaryOp { operator, factor: Box::new(nested_expression)})
            },
            _ => Err(anyhow!("Could not parse factor"))
        }
    }

    fn get_next_token_from_iter<'a>(token_iter: &mut Peekable<Iter<'a, TokenType>>) -> anyhow::Result<&'a TokenType>{
        token_iter.next().context(anyhow!("no next token"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_binary_op_subtraction() {
        let token_vec = vec![TokenType::IntLiteral(1), TokenType::Minus, TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter().peekable());
        assert_eq!(
            exp.unwrap(), 
            AstNode::BinaryOp { 
                operator: Operator::Subtraction, 
                term: Box::new( AstNode::Constant { constant: 1 } ), 
                next_term: Box::new( AstNode::Constant { constant: 2 }),
            },
        )
    }

    #[test]
    fn test_parse_binary_op_multiplication() {
        let token_vec = vec![TokenType::IntLiteral(1), TokenType::Multiplication, TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter().peekable());
        assert_eq!(
            exp.unwrap(), 
            AstNode::BinaryOp { 
                operator: Operator::Multiplication, 
                term: Box::new( AstNode::Constant { constant: 1 } ), 
                next_term: Box::new( AstNode::Constant { constant: 2 }),
            },
        )
    }

    #[test]
    fn test_parse_binary_op_nested_add_multiply() {
        // 1 + 2 * 3
        let token_vec = vec![
            TokenType::IntLiteral(1), 
            TokenType::Addition, 
            TokenType::IntLiteral(2), 
            TokenType::Multiplication, 
            TokenType::IntLiteral(3),
        ];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter().peekable());
        assert_eq!(
            exp.unwrap(), 
            AstNode::BinaryOp { 
                operator: Operator::Addition, 
                term: Box::new( AstNode::Constant { constant: 1 } ), 
                next_term: Box::new( 
                    AstNode::BinaryOp { 
                        operator: Operator::Multiplication,
                        term: Box::new( AstNode::Constant { constant: 2 }),
                        next_term: Box::new( AstNode::Constant { constant: 3 }),
                    }
                ),
            },
        )
    }

    #[test]
    fn test_parse_binary_op_nested_add_multiply_parentheses() {
        // (1 + 2) * 3
        let token_vec = vec![
            TokenType::OpenParens,
            TokenType::IntLiteral(1), 
            TokenType::Addition, 
            TokenType::IntLiteral(2), 
            TokenType::ClosedParens,
            TokenType::Multiplication, 
            TokenType::IntLiteral(3),
        ];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter().peekable());
        assert_eq!(
            exp.unwrap(), 
            AstNode::BinaryOp { 
                operator: Operator::Multiplication, 
                term: Box::new(
                    AstNode::BinaryOp { 
                        operator: Operator::Addition,
                        term: Box::new( AstNode::Constant { constant: 1 }),
                        next_term: Box::new( AstNode::Constant { constant: 2 }),
                    }
                ),
                next_term: Box::new( AstNode::Constant { constant: 3 } ),
            },
        )
    }

    #[test]
    fn test_parse_unary_op() {
        let token_vec = vec![TokenType::BitwiseComplement, TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter().peekable());
        assert_eq!(
            exp.unwrap(), 
            AstNode::UnaryOp { 
                operator: Operator::BitwiseComplement, 
                factor: Box::new(AstNode::Constant { constant: 2 }),
            }
        );
    }

    #[test]
    fn test_parse_unary_op_nested() {
        let token_vec = vec![TokenType::BitwiseComplement, TokenType::BitwiseComplement, TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter().peekable());
        assert_eq!(
            exp.unwrap(), 
            AstNode::UnaryOp { 
                operator: Operator::BitwiseComplement, 
                factor: Box::new(
                    AstNode::UnaryOp { 
                        operator: Operator::BitwiseComplement, 
                        factor: Box::new(
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
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter().peekable());
        assert_eq!(exp.unwrap(), AstNode::Constant{constant: 2});
    }

    #[test]
    fn test_parse_statement() {
        let token_vec = vec![TokenType::Keyword("return".into()), TokenType::IntLiteral(2), TokenType::Semicolon];
        let statement: anyhow::Result<AstNode> = AstNode::parse_statement(&mut token_vec.iter().peekable());
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
        let function: anyhow::Result<AstNode> = AstNode::parse_function(&mut token_vec.iter().peekable());
        let expression = Box::new(AstNode::Constant { constant: 2 });
        let statement = Box::new(AstNode::Statement {expression});
        assert_eq!(function.unwrap(), AstNode::Function { identifier: "main".into(), statement });
    }
}