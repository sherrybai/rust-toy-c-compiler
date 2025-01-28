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
    Division,
    AND,
    OR,
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual
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
            TokenType::AND => Ok(Self::AND),
            TokenType::OR => Ok(Self::OR),
            TokenType::Equal => Ok(Self::Equal),
            TokenType::NotEqual => Ok(Self::NotEqual),
            TokenType::LessThan => Ok(Self::LessThan),
            TokenType::LessThanOrEqual => Ok(Self::LessThanOrEqual),
            TokenType::GreaterThan => Ok(Self::GreaterThan),
            TokenType::GreaterThanOrEqual => Ok(Self::GreaterThanOrEqual),
            _ => Err(anyhow!("Unsupported operator"))
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum AstNode {
    Program {
        function_list: Vec<Box<Self>>,
    },
    Function {
        function_name: String,
        parameters: Vec<String>,
        statement: Box<Self>,
    },
    Statement {
        expression: Box<Self>,
    },
    // Expressions
    BinaryOp {
        operator: Operator,
        expression: Box<Self>,      
        next_expression: Box<Self>,
    },
    UnaryOp {
        operator: Operator,
        factor: Box<Self>,
    },
    Constant {
        constant: u32,
    },
    FunctionCall {
        function_name: String,
        parameters: Vec<Box<Self>>,
    }
}

impl AstNode {
    pub fn parse(tokens: &[TokenType]) -> anyhow::Result<Self> {
        // <program> ::= { <function> }
        let mut token_iter = tokens.iter().peekable();
        let mut function_list: Vec<Box<Self>> = Vec::new();
        loop {
            let next_token: Option<&&TokenType> = token_iter.peek();
            match next_token {
                Some(_) => {
                    let function: Self = Self::parse_function(&mut token_iter)?;
                    function_list.push(Box::new(function));
                }
                None => {
                    return Ok(Self::Program{ function_list })
                }
            }
        }
    }

    fn parse_function(token_iter: &mut Peekable<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <function> ::= "int" <id> "(" [ "int" <id> { "," "int" <id> } ] ")" ( "{" { <block-item> } "}" | ";" )

        // parse keyword token
        if let TokenType::Keyword(s) = Self::get_next_token_from_iter(token_iter)? {
            if s != "int"  {
                return Err(anyhow!("First keyword of function is not 'int'"));
            }
        }
        else {
            return Err(anyhow!("First token of function is not a keyword"));
        }

        // Parse function name
        let function_name: String;
        if let TokenType::Identifier(s) = Self::get_next_token_from_iter(token_iter)? {
            function_name = s.to_string();
        } else {
            return Err(anyhow!("No function identifier found"));
        }

        let TokenType::OpenParens = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("No open parens"));
        };

        // parse parameters
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        let mut parameters: Vec<String> = Vec::new();
        while let Some(TokenType::Identifier(param)) = next_token {
            // advance the iterator
            Self::get_next_token_from_iter(token_iter)?;
            parameters.push(param.clone());
            next_token = token_iter.peek();
        }

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
        Ok(Self::Function { function_name, parameters, statement: Box::new(statement) })

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
        // <exp> ::= <logical-and-exp> { "||" <logical-and-exp> }
        let mut logical_or_exp = Self::parse_logical_and_exp(token_iter)?;
        
        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(TokenType::OR) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_logical_or_exp = Self::parse_logical_and_exp(token_iter)?;
            logical_or_exp = AstNode::BinaryOp{ 
                operator: Operator::get_binary_op_from_token(token)?, 
                expression: Box::new(logical_or_exp), 
                next_expression: Box::new(next_logical_or_exp)
            };

            next_token = token_iter.peek();
        }

        Ok(logical_or_exp)
    }

    fn parse_logical_and_exp(token_iter: &mut Peekable<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <logical-and-exp> ::= <equality-exp> { "&&" <equality-exp> }
        let mut logical_and_exp = Self::parse_equality_exp(token_iter)?;
        
        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(TokenType::AND) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_logical_and_exp = Self::parse_equality_exp(token_iter)?;
            logical_and_exp = AstNode::BinaryOp{ 
                operator: Operator::get_binary_op_from_token(token)?, 
                expression: Box::new(logical_and_exp), 
                next_expression: Box::new(next_logical_and_exp)
            };

            next_token = token_iter.peek();
        }

        Ok(logical_and_exp)

    }

    fn parse_equality_exp(token_iter: &mut Peekable<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <equality-exp> ::= <relational-exp> { ("!=" | "==") <relational-exp> }
        let mut equality_exp = Self::parse_relational_exp(token_iter)?;
        
        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(TokenType::Equal | TokenType::NotEqual) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_equality_exp = Self::parse_relational_exp(token_iter)?;
            equality_exp = AstNode::BinaryOp{ 
                operator: Operator::get_binary_op_from_token(token)?, 
                expression: Box::new(equality_exp), 
                next_expression: Box::new(next_equality_exp)
            };

            next_token = token_iter.peek();
        }

        Ok(equality_exp)
    }

    fn parse_relational_exp(token_iter: &mut Peekable<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <relational-exp> ::= <additive-exp> { ("<" | ">" | "<=" | ">=") <additive-exp> }
        let mut additive_exp = Self::parse_additive_exp(token_iter)?;
        
        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(
            TokenType::LessThan | TokenType::GreaterThan | TokenType::LessThanOrEqual | TokenType::GreaterThanOrEqual
        ) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_additive_exp = Self::parse_additive_exp(token_iter)?;
            additive_exp = AstNode::BinaryOp{ 
                operator: Operator::get_binary_op_from_token(token)?, 
                expression: Box::new(additive_exp), 
                next_expression: Box::new(next_additive_exp)
            };

            next_token = token_iter.peek();
        }

        Ok(additive_exp)
    }

    fn parse_additive_exp(token_iter: &mut Peekable<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <additive_exp> ::= <term> { ("+" | "-") <term> }
        let mut term = Self::parse_term(token_iter)?;

        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(TokenType::Addition | TokenType::Minus) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_term = Self::parse_term(token_iter)?;
            term = AstNode::BinaryOp{ 
                operator: Operator::get_binary_op_from_token(token)?, 
                expression: Box::new(term), 
                next_expression: Box::new(next_term),
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
                expression: Box::new(factor),
                next_expression: Box::new(next_factor),
            };

            next_token = token_iter.peek();
        }

        Ok(factor)
    }

    fn parse_factor(token_iter: &mut Peekable<Iter<TokenType>>) -> anyhow::Result<Self> {
        // factor: operand of multiplication/division
        // <factor> ::= <function-call> | "(" <exp> ")" | <unary_op> <factor> | <int>

        let token = Self::get_next_token_from_iter(token_iter)?;

        match token {
            TokenType::Identifier(function_name) => {
                let TokenType::OpenParens = Self::get_next_token_from_iter(token_iter)? else {
                    return Err(anyhow!("Function call missing open parens"))
                };

                // parse list of expression params
                let mut parameters: Vec<Box<Self>> = Vec::new();

                let next_token: Option<&&TokenType> = token_iter.peek();
                if let Some(TokenType::ClosedParens) = next_token {
                    // do nothing
                } else {
                    // parse at least one param
                    let exp = Self::parse_expression(token_iter)?;
                    parameters.push(Box::new(exp));
                    loop {
                        let next_token: Option<&&TokenType> = token_iter.peek();
                        if let Some(TokenType::ClosedParens) = next_token {
                            break;
                        }
                        // parse comma if expression list isn't over
                        let TokenType::Comma = Self::get_next_token_from_iter(token_iter)? else {
                            return Err(anyhow!("Function call params must be delineated with commas"))
                        };
                        // parse next expression
                        let exp = Self::parse_expression(token_iter)?;
                        parameters.push(Box::new(exp));
                    }
                    let TokenType::ClosedParens = Self::get_next_token_from_iter(token_iter)? else {
                        // this should not happen: loop breaks once closed parens is found
                        return Err(anyhow!("Function call missing closed parens"))
                    };
                }
                Ok(Self::FunctionCall { function_name: function_name.clone(), parameters })
            }
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
    fn test_parse_function_call() {
        let token_vec = vec![
            TokenType::Identifier("main".into()),
            TokenType::OpenParens,
            TokenType::IntLiteral(1),
            TokenType::Comma,
            TokenType::IntLiteral(2),
            TokenType::Comma,
            TokenType::IntLiteral(3),
            TokenType::ClosedParens,
        ];
        let function: anyhow::Result<AstNode> = AstNode::parse_factor(&mut token_vec.iter().peekable());
        assert_eq!(
            function.unwrap(), 
            AstNode::FunctionCall {
                function_name: "main".into(), 
                parameters: vec![
                    Box::new(AstNode::Constant { constant: 1 }),
                    Box::new(AstNode::Constant { constant: 2 }),
                    Box::new(AstNode::Constant { constant: 3 }),
                ], 
            }
        );
    }

    #[test]
    fn test_parse_and_or_equality() {
        let token_vec = vec![
            TokenType::IntLiteral(2), 
            TokenType::Equal, 
            TokenType::IntLiteral(2), 
            TokenType::OR, 
            TokenType::IntLiteral(0), 
        ];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter().peekable());
        assert_eq!(
            exp.unwrap(), 
            AstNode::BinaryOp { 
                operator: Operator::OR,
                expression: Box::new(
                    AstNode::BinaryOp { 
                        operator: Operator::Equal, 
                        expression: Box::new( AstNode::Constant { constant: 2 } ), 
                        next_expression: Box::new( AstNode::Constant { constant: 2 }),
                    }
                ),
                next_expression: Box::new(
                    AstNode::Constant { constant: 0 }
                ),
            }
        )
    }

    #[test]
    fn test_parse_binary_op_and_or() {
        let token_vec = vec![
            TokenType::IntLiteral(1), 
            TokenType::OR,
            TokenType::IntLiteral(2),
            TokenType::AND,
            TokenType::IntLiteral(3)
        ];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter().peekable());
        assert_eq!(
            exp.unwrap(), 
            AstNode::BinaryOp { 
                operator: Operator::OR,
                expression: Box::new(
                    AstNode::Constant { constant: 1 }
                ),
                next_expression: Box::new(
                    AstNode::BinaryOp { 
                        operator: Operator::AND, 
                        expression: Box::new( AstNode::Constant { constant: 2 } ), 
                        next_expression: Box::new( AstNode::Constant { constant: 3 }),
                    }
                ),
            }
        )
    }

    #[test]
    fn test_parse_binary_op_subtraction() {
        let token_vec = vec![TokenType::IntLiteral(1), TokenType::Minus, TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> = AstNode::parse_expression(&mut token_vec.iter().peekable());
        assert_eq!(
            exp.unwrap(), 
            AstNode::BinaryOp { 
                operator: Operator::Subtraction, 
                expression: Box::new( AstNode::Constant { constant: 1 } ), 
                next_expression: Box::new( AstNode::Constant { constant: 2 }),
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
                expression: Box::new( AstNode::Constant { constant: 1 } ), 
                next_expression: Box::new( AstNode::Constant { constant: 2 }),
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
                expression: Box::new( AstNode::Constant { constant: 1 } ), 
                next_expression: Box::new( 
                    AstNode::BinaryOp { 
                        operator: Operator::Multiplication,
                        expression: Box::new( AstNode::Constant { constant: 2 }),
                        next_expression: Box::new( AstNode::Constant { constant: 3 }),
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
                expression: Box::new(
                    AstNode::BinaryOp { 
                        operator: Operator::Addition,
                        expression: Box::new( AstNode::Constant { constant: 1 }),
                        next_expression: Box::new( AstNode::Constant { constant: 2 }),
                    }
                ),
                next_expression: Box::new( AstNode::Constant { constant: 3 } ),
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
            TokenType::Identifier("param1".into()),
            TokenType::Identifier("param2".into()),
            TokenType::Identifier("param3".into()),
            TokenType::ClosedParens,
            TokenType::OpenBrace,
            TokenType::Keyword("return".into()), 
            TokenType::IntLiteral(2), TokenType::Semicolon,
            TokenType::ClosedBrace
        ];
        let function: anyhow::Result<AstNode> = AstNode::parse_function(&mut token_vec.iter().peekable());
        let expression = Box::new(AstNode::Constant { constant: 2 });
        let statement = Box::new(AstNode::Statement {expression});
        assert_eq!(
            function.unwrap(), 
            AstNode::Function { 
                function_name: "main".into(), 
                parameters: vec![
                    "param1".into(), 
                    "param2".into(), 
                    "param3".into()
                ], 
                statement 
            }
        );
    }

    #[test]
    fn test_parse_program_multiple_func() {
        let token_vec = vec![
            // first function
            TokenType::Keyword("int".into()),
            TokenType::Identifier("helper".into()),
            TokenType::OpenParens,
            TokenType::Identifier("param1".into()),
            TokenType::Identifier("param2".into()),
            TokenType::Identifier("param3".into()),
            TokenType::ClosedParens,
            TokenType::OpenBrace,
            TokenType::Keyword("return".into()), 
            TokenType::IntLiteral(1), TokenType::Semicolon,
            TokenType::ClosedBrace,
            // main function        
            TokenType::Keyword("int".into()),
            TokenType::Identifier("main".into()),
            TokenType::OpenParens,
            TokenType::ClosedParens,
            TokenType::OpenBrace,
            TokenType::Keyword("return".into()), 
            TokenType::IntLiteral(2), TokenType::Semicolon,
            TokenType::ClosedBrace
        ];

        let program: anyhow::Result<AstNode> = AstNode::parse(&token_vec);
        assert_eq!(
            program.unwrap(), 
            AstNode::Program { 
                function_list: vec![
                    Box::new(
                        AstNode::Function { 
                            function_name: "helper".into(), 
                            parameters: vec![
                                "param1".into(),
                                "param2".into(),
                                "param3".into(),
                            ], 
                            statement: Box::new(
                                AstNode::Statement { 
                                    expression: Box::new(
                                        AstNode::Constant{ constant: 1 }
                                    ),
                                },
                            ),
                        }
                    ),
                    Box::new(
                        AstNode::Function { 
                            function_name: "main".into(), 
                            parameters: vec![], 
                            statement: Box::new(
                                AstNode::Statement { 
                                    expression: Box::new(
                                        AstNode::Constant{ constant: 2 }
                                    ),
                                },
                            ),
                        }
                    ),
                ]
            }
        );
    }
}