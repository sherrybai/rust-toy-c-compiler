use std::slice::Iter;

use crate::lexer::TokenType;
use anyhow::anyhow;
use anyhow::Context;
use itertools::peek_nth;
use itertools::PeekNth;

#[derive(Debug, PartialEq)]
pub enum Operator {
    Negation,
    BitwiseComplement,
    LogicalNegation,
    Subtraction,
    Addition,
    Multiplication,
    Division,
    And,
    Or,
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
}

impl Operator {
    fn get_unary_op_from_token(t: &TokenType) -> anyhow::Result<Self> {
        match t {
            TokenType::Minus => Ok(Self::Negation),
            TokenType::BitwiseComplement => Ok(Self::BitwiseComplement),
            TokenType::LogicalNegation => Ok(Self::LogicalNegation),
            _ => Err(anyhow!("Unsupported operator")),
        }
    }

    fn get_binary_op_from_token(t: &TokenType) -> anyhow::Result<Self> {
        match t {
            TokenType::Minus => Ok(Self::Subtraction),
            TokenType::Addition => Ok(Self::Addition),
            TokenType::Multiplication => Ok(Self::Multiplication),
            TokenType::Division => Ok(Self::Division),
            TokenType::And => Ok(Self::And),
            TokenType::Or => Ok(Self::Or),
            TokenType::Equal => Ok(Self::Equal),
            TokenType::NotEqual => Ok(Self::NotEqual),
            TokenType::LessThan => Ok(Self::LessThan),
            TokenType::LessThanOrEqual => Ok(Self::LessThanOrEqual),
            TokenType::GreaterThan => Ok(Self::GreaterThan),
            TokenType::GreaterThanOrEqual => Ok(Self::GreaterThanOrEqual),
            _ => Err(anyhow!("Unsupported operator")),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum AstNode {
    Program {
        function_list: Vec<Self>,
    },
    Function {
        function_name: String,
        parameters: Vec<String>,
        body: Option<Box<Self>>,
    },
    // Statements
    Return {
        expression: Box<Self>,
    },
    Assign {
        variable: String,
        expression: Box<Self>,
    },
    If {
        condition: Box<Self>,
        if_statement: Box<Self>,
        else_statement: Option<Box<Self>>,
    },
    For {
        initial_decl_or_exp: Box<Self>,
        condition: Box<Self>,
        post_condition: Box<Self>,
        body: Box<Self>,
    },
    While {
        condition: Box<Self>,
        body: Box<Self>,
    },
    Do {
        body: Box<Self>,
        condition: Box<Self>,
    },
    Break,
    Continue,
    Compound {
        block_item_list: Vec<Self>,
    },
    // Other block items
    Declare {
        variable: String,
        expression: Option<Box<Self>>,
    },
    // Expressions
    NullExpression,
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
    Variable {
        variable: String,
    },
    Conditional {
        condition: Box<Self>,
        if_expression: Box<Self>,
        else_expression: Box<Self>,
    },
    FunctionCall {
        function_name: String,
        parameters: Vec<Self>,
    },
}

impl AstNode {
    pub fn parse(tokens: &[TokenType]) -> anyhow::Result<Self> {
        // <program> ::= { <function> }
        let mut token_iter = peek_nth(tokens.iter());
        let mut function_list: Vec<Self> = Vec::new();
        loop {
            let next_token: Option<&&TokenType> = token_iter.peek();
            match next_token {
                Some(_) => {
                    let function: Self = Self::parse_function(&mut token_iter)?;
                    function_list.push(function);
                }
                None => return Ok(Self::Program { function_list }),
            }
        }
    }

    fn parse_function(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <function> ::= "int" <id> "(" [ "int" <id> { "," "int" <id> } ] ")" ( "{" { <block-item> } "}" | ";" )

        // parse keyword token
        if let TokenType::Keyword(s) = Self::get_next_token_from_iter(token_iter)? {
            if s != "int" {
                return Err(anyhow!("First keyword of function is not 'int'"));
            }
        } else {
            return Err(anyhow!("First token of function is not a keyword"));
        }

        // parse function name
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

        if let Some(next_token) = token_iter.peek() {
            match next_token {
                TokenType::Semicolon => {
                    // advance past semicolon
                    Self::get_next_token_from_iter(token_iter)?;
                    // function declaration
                    return Ok(Self::Function {
                        function_name,
                        parameters,
                        body: None,
                    });
                }
                TokenType::OpenBrace => {
                    // parse compound statement
                    let statement = Self::parse_statement(token_iter)?;
                    return Ok(Self::Function {
                        function_name,
                        parameters,
                        body: Some(Box::new(statement)),
                    });
                }
                _ => {
                    return Err(anyhow!(
                        "No semicolon or open brace following function parameters"
                    ));
                }
            }
        } else {
            return Err(anyhow!("Missing token after function parameters"));
        };
    }

    fn parse_block_item(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <block-item> ::= <statement> | <declaration>
        // <declaration> ::= "int" <id> [ = <exp> ] ";"
        if let Some(TokenType::Keyword(s)) = token_iter.peek() {
            if s == "int" {
                return Ok(Self::parse_declaration(token_iter)?);
            }
        }
        Ok(Self::parse_statement(token_iter)?)
    }

    fn parse_declaration(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // variable declaration
        // advance iterator past "int"
        Self::get_next_token_from_iter(token_iter)?;
        let TokenType::Identifier(variable_name) = Self::get_next_token_from_iter(token_iter)?
        else {
            return Err(anyhow!(
                "int keyword must be followed by string identifier for variable declaration"
            ));
        };

        // check for assignment
        let mut expression: Option<Box<Self>> = None;
        if let Some(TokenType::Assignment) = token_iter.peek() {
            // advance iterator past "="
            Self::get_next_token_from_iter(token_iter)?;
            expression = Some(Box::new(Self::parse_expression(token_iter)?));
        }

        // must end in semicolon
        let TokenType::Semicolon = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("Statement does not end in semicolon"));
        };

        Ok(Self::Declare {
            variable: variable_name.clone(),
            expression,
        })
    }

    fn parse_statement(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <statement> ::= "return" <exp-option> ";"| <exp> ";"
        // | <if-statement> | <for-statement> | <while-statement> | <do-statement>
        // | "break" ";" | "continue" ";"
        let statement: AstNode;
        let next_token: Option<&&TokenType> = token_iter.peek();
        match next_token {
            Some(TokenType::Keyword(s)) => {
                match &s[..] {
                    "return" => {
                        // advance iterator past "return"
                        Self::get_next_token_from_iter(token_iter)?;

                        let expression = Self::parse_expression(token_iter)?;
                        statement = Self::Return {
                            expression: Box::new(expression),
                        };
                        // must end in semicolon
                        let TokenType::Semicolon = Self::get_next_token_from_iter(token_iter)?
                        else {
                            return Err(anyhow!("Statement does not end in semicolon"));
                        };
                    }
                    "if" => {
                        statement = Self::parse_if_statement(token_iter)?;
                    }
                    "for" => {
                        statement = Self::parse_for_statement(token_iter)?;
                    }
                    "while" => {
                        statement = Self::parse_while_statement(token_iter)?;
                    }
                    "do" => {
                        statement = Self::parse_do_statement(token_iter)?;
                    }
                    "break" => {
                        // advance iterator past "break"
                        Self::get_next_token_from_iter(token_iter)?;
                        statement = Self::Break;

                        let TokenType::Semicolon = Self::get_next_token_from_iter(token_iter)?
                        else {
                            return Err(anyhow!("Statement does not end in semicolon"));
                        };
                    }
                    "continue" => {
                        // advance iterator past "continue"
                        Self::get_next_token_from_iter(token_iter)?;
                        statement = Self::Continue;

                        let TokenType::Semicolon = Self::get_next_token_from_iter(token_iter)?
                        else {
                            return Err(anyhow!("Statement does not end in semicolon"));
                        };
                    }
                    _ => {
                        return Err(anyhow!("Unknown keyword"));
                    }
                }
            }
            Some(TokenType::OpenBrace) => {
                // compound statement
                // advance past {
                Self::get_next_token_from_iter(token_iter)?;

                // parse statements
                let mut block_items = Vec::new();
                let mut next_token: Option<&&TokenType> = token_iter.peek();
                loop {
                    if let Some(TokenType::ClosedBrace) = next_token {
                        // terminate function body with closed brace
                        Self::get_next_token_from_iter(token_iter)?;
                        break;
                    } else {
                        let statement = Self::parse_block_item(token_iter)?;
                        block_items.push(statement);
                    };
                    next_token = token_iter.peek();
                }

                return Ok(Self::Compound {
                    block_item_list: block_items,
                });
            }
            _ => {
                // parse as expression
                statement = Self::parse_expression(token_iter)?;
                // must end in semicolon
                let TokenType::Semicolon = Self::get_next_token_from_iter(token_iter)? else {
                    return Err(anyhow!("Statement does not end in semicolon"));
                };
            }
        }

        // return node
        Ok(statement)
    }

    fn parse_if_statement(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <if-statement> ::= "if" "(" <exp> ")" <statement> [ "else" <statement> ] | | "{" { <block-item> } "}

        // advance iterator past "if"
        Self::get_next_token_from_iter(token_iter)?;

        if let TokenType::OpenParens = Self::get_next_token_from_iter(token_iter)? {
            // do nothing
        } else {
            return Err(anyhow!("if keyword must be followed by parentheses"));
        }

        // parse condition
        let expression = Box::new(Self::parse_expression(token_iter)?);

        if let TokenType::ClosedParens = Self::get_next_token_from_iter(token_iter)? {
            // do nothing
        } else {
            return Err(anyhow!("if parentheses not closed"));
        }

        // parse if statement
        let if_statement = Box::new(Self::parse_statement(token_iter)?);

        // optional else statement
        let mut else_statement: Option<Box<AstNode>> = None;
        if let Some(TokenType::Keyword(s)) = token_iter.peek() {
            if s == "else" {
                // advance iterator past else
                Self::get_next_token_from_iter(token_iter)?;

                // parse else statement
                else_statement = Some(Box::new(Self::parse_statement(token_iter)?));
            }
        }

        Ok(Self::If {
            condition: expression,
            if_statement,
            else_statement,
        })
    }

    fn parse_for_statement(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <for-statement> ::= "for" "(" <exp-option> ";" <exp-option> ";" <exp-option> ")" <statement>
        // | "for" "(" <declaration> <exp-option> ";" <exp-option> ")" <statement>

        // iterate past "for" keyword
        Self::get_next_token_from_iter(token_iter)?;

        // open parens
        let TokenType::OpenParens = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("for keyword must be succeeded by parentheses"));
        };

        let initial_decl_or_exp: Self;
        if let Some(TokenType::Keyword(s)) = token_iter.peek() {
            if s == "int" {
                // parse declaration
                initial_decl_or_exp = Self::parse_declaration(token_iter)?;
            } else {
                initial_decl_or_exp = Self::parse_expression(token_iter)?;
                let TokenType::Semicolon = Self::get_next_token_from_iter(token_iter)? else {
                    return Err(anyhow!("For loop missing semicolon"));
                };
            }
        } else {
            initial_decl_or_exp = Self::parse_expression(token_iter)?;
            let TokenType::Semicolon = Self::get_next_token_from_iter(token_iter)? else {
                return Err(anyhow!("For loop missing semicolon"));
            };
        }

        // parse expressions
        let condition = Self::parse_expression(token_iter)?;
        let TokenType::Semicolon = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("For loop missing semicolon"));
        };

        let post_condition = Self::parse_expression(token_iter)?;
        // closed parens
        let TokenType::ClosedParens = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("for loop parentheses not closed"));
        };

        // body is compound statement
        let body: AstNode = Self::parse_statement(token_iter)?;

        Ok(Self::For {
            initial_decl_or_exp: Box::new(initial_decl_or_exp),
            condition: Box::new(condition),
            post_condition: Box::new(post_condition),
            body: Box::new(body),
        })
    }

    fn parse_while_statement(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <while-statement> ::= "while" "(" <exp> ")" <statement>

        // iterate past "while" keyword
        Self::get_next_token_from_iter(token_iter)?;

        // open parens
        let TokenType::OpenParens = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("while keyword must be succeeded by parentheses"));
        };

        // parse condition expression
        let condition = Self::parse_expression(token_iter)?;

        // closed parens
        let TokenType::ClosedParens = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("while loop parentheses not closed"));
        };

        // parse body
        let body: AstNode = Self::parse_statement(token_iter)?;

        Ok(Self::While {
            condition: Box::new(condition),
            body: Box::new(body),
        })
    }

    fn parse_do_statement(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <do-statement> ::= "do" <statement> "while" "(" <exp> ")" ";"

        // iterate past "do" keyword
        Self::get_next_token_from_iter(token_iter)?;

        // parse body
        let body: AstNode = Self::parse_statement(token_iter)?;

        // "while" keyword
        let TokenType::Keyword(s) = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("do statement must be succeeded by 'while' keyword"));
        };
        if s != "while" {
            return Err(anyhow!("do statement must be succeeded by 'while' keyword"));
        }

        // open parens
        let TokenType::OpenParens = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("while keyword must be succeeded by parentheses"));
        };

        // parse condition expression
        let condition = Self::parse_expression(token_iter)?;

        // closed parens
        let TokenType::ClosedParens = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("do-while loop parentheses not closed"));
        };

        // semicolon
        let TokenType::Semicolon = Self::get_next_token_from_iter(token_iter)? else {
            return Err(anyhow!("do-while loop must be succeeded by semicolon"));
        };

        Ok(Self::Do {
            body: Box::new(body),
            condition: Box::new(condition),
        })
    }

    fn parse_expression(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <exp-option> ::= <exp> | ""
        // <exp> ::= <id> "=" <exp> | <conditional-exp>
        // expression option
        // if next token is semicolon or closed parentheses, this is a null expression
        if let Some(TokenType::Semicolon) = token_iter.peek() {
            return Ok(Self::NullExpression);
        }
        if let Some(TokenType::ClosedParens) = token_iter.peek() {
            return Ok(Self::NullExpression);
        }

        let mut next_token: Option<&&TokenType> = token_iter.peek();
        if let Some(TokenType::Identifier(variable_name)) = next_token {
            // peek forward twice to check for '='
            next_token = token_iter.peek_nth(1);
            if let Some(TokenType::Assignment) = next_token {
                // advance twice
                Self::get_next_token_from_iter(token_iter)?;
                Self::get_next_token_from_iter(token_iter)?;

                // parse expression
                let expression = Self::parse_expression(token_iter)?;
                return Ok(Self::Assign {
                    variable: variable_name.clone(),
                    expression: Box::new(expression),
                });
            } else {
                // do nothing
            }
        }
        // not an assignment
        Self::parse_conditional_exp(token_iter)
    }

    fn parse_conditional_exp(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <conditional-exp> ::= <logical-or-exp> [ "?" <exp> ":" <conditional-exp> ]
        let logical_or_exp = Self::parse_logical_or_exp(token_iter)?;

        // parse question mark
        if let Some(TokenType::QuestionMark) = token_iter.peek() {
            // advance iterator
            Self::get_next_token_from_iter(token_iter)?;
            // ternary operator
            let if_expression: AstNode = Self::parse_expression(token_iter)?;
            let else_expression: AstNode;
            if let TokenType::Colon = Self::get_next_token_from_iter(token_iter)? {
                else_expression = Self::parse_conditional_exp(token_iter)?;
            } else {
                return Err(anyhow!("Missing colon in ternary operator expression"));
            }
            Ok(AstNode::Conditional {
                condition: Box::new(logical_or_exp),
                if_expression: Box::new(if_expression),
                else_expression: Box::new(else_expression),
            })
        } else {
            Ok(logical_or_exp)
        }
    }

    fn parse_logical_or_exp(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <exp> ::=  <logical-and-exp> { "||" <logical-and-exp> }
        let mut logical_or_exp = Self::parse_logical_and_exp(token_iter)?;

        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(TokenType::Or) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_logical_or_exp = Self::parse_logical_and_exp(token_iter)?;
            logical_or_exp = AstNode::BinaryOp {
                operator: Operator::get_binary_op_from_token(token)?,
                expression: Box::new(logical_or_exp),
                next_expression: Box::new(next_logical_or_exp),
            };

            next_token = token_iter.peek();
        }

        Ok(logical_or_exp)
    }

    fn parse_logical_and_exp(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <logical-and-exp> ::= <equality-exp> { "&&" <equality-exp> }
        let mut logical_and_exp = Self::parse_equality_exp(token_iter)?;

        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(TokenType::And) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_logical_and_exp = Self::parse_equality_exp(token_iter)?;
            logical_and_exp = AstNode::BinaryOp {
                operator: Operator::get_binary_op_from_token(token)?,
                expression: Box::new(logical_and_exp),
                next_expression: Box::new(next_logical_and_exp),
            };

            next_token = token_iter.peek();
        }

        Ok(logical_and_exp)
    }

    fn parse_equality_exp(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <equality-exp> ::= <relational-exp> { ("!=" | "==") <relational-exp> }
        let mut equality_exp = Self::parse_relational_exp(token_iter)?;

        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(TokenType::Equal | TokenType::NotEqual) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_equality_exp = Self::parse_relational_exp(token_iter)?;
            equality_exp = AstNode::BinaryOp {
                operator: Operator::get_binary_op_from_token(token)?,
                expression: Box::new(equality_exp),
                next_expression: Box::new(next_equality_exp),
            };

            next_token = token_iter.peek();
        }

        Ok(equality_exp)
    }

    fn parse_relational_exp(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <relational-exp> ::= <additive-exp> { ("<" | ">" | "<=" | ">=") <additive-exp> }
        let mut additive_exp = Self::parse_additive_exp(token_iter)?;

        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(
            TokenType::LessThan
            | TokenType::GreaterThan
            | TokenType::LessThanOrEqual
            | TokenType::GreaterThanOrEqual,
        ) = next_token
        {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_additive_exp = Self::parse_additive_exp(token_iter)?;
            additive_exp = AstNode::BinaryOp {
                operator: Operator::get_binary_op_from_token(token)?,
                expression: Box::new(additive_exp),
                next_expression: Box::new(next_additive_exp),
            };

            next_token = token_iter.peek();
        }

        Ok(additive_exp)
    }

    fn parse_additive_exp(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // <additive_exp> ::= <term> { ("+" | "-") <term> }
        let mut term = Self::parse_term(token_iter)?;

        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(TokenType::Addition | TokenType::Minus) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_term = Self::parse_term(token_iter)?;
            term = AstNode::BinaryOp {
                operator: Operator::get_binary_op_from_token(token)?,
                expression: Box::new(term),
                next_expression: Box::new(next_term),
            };

            next_token = token_iter.peek();
        }

        Ok(term)
    }

    fn parse_term(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // term: operand of addition/subtraction
        // <term> ::= <factor> { ("*" | "/") <factor> }

        let mut factor = Self::parse_factor(token_iter)?;

        // keep parsing subsequent terms, wrapping each new one around old ones
        let mut next_token: Option<&&TokenType> = token_iter.peek();
        while let Some(TokenType::Multiplication | TokenType::Division) = next_token {
            // advance the iterator (token = *next_token)
            let token = Self::get_next_token_from_iter(token_iter)?;

            let next_factor = Self::parse_factor(token_iter)?;
            factor = AstNode::BinaryOp {
                operator: Operator::get_binary_op_from_token(token)?,
                expression: Box::new(factor),
                next_expression: Box::new(next_factor),
            };

            next_token = token_iter.peek();
        }

        Ok(factor)
    }

    fn parse_factor(token_iter: &mut PeekNth<Iter<TokenType>>) -> anyhow::Result<Self> {
        // factor: operand of multiplication/division
        // <factor> ::= <function-call> | "(" <exp> ")" | <unary_op> <factor> | <int> | <id>
        let token = Self::get_next_token_from_iter(token_iter)?;

        match token {
            TokenType::Identifier(identifier) => {
                let next_token = token_iter.peek();
                // function call
                if let Some(TokenType::OpenParens) = next_token {
                    // advance iterator past '('
                    Self::get_next_token_from_iter(token_iter)?;

                    // parse list of expression params
                    let mut parameters: Vec<Self> = Vec::new();

                    let next_token: Option<&&TokenType> = token_iter.peek();
                    if let Some(TokenType::ClosedParens) = next_token {
                        // do nothing
                    } else {
                        // parse at least one param
                        let exp = Self::parse_expression(token_iter)?;
                        parameters.push(exp);
                        loop {
                            let next_token: Option<&&TokenType> = token_iter.peek();
                            if let Some(TokenType::ClosedParens) = next_token {
                                break;
                            }
                            // parse comma if expression list isn't over
                            let TokenType::Comma = Self::get_next_token_from_iter(token_iter)?
                            else {
                                return Err(anyhow!(
                                    "Function call params must be delineated with commas"
                                ));
                            };
                            // parse next expression
                            let exp = Self::parse_expression(token_iter)?;
                            parameters.push(exp);
                        }
                        let TokenType::ClosedParens = Self::get_next_token_from_iter(token_iter)?
                        else {
                            // this should not happen: loop breaks once closed parens is found
                            return Err(anyhow!("Function call missing closed parens"));
                        };
                    }
                    Ok(Self::FunctionCall {
                        function_name: identifier.clone(),
                        parameters,
                    })
                } else {
                    // factor can be local variable
                    Ok(Self::Variable {
                        variable: identifier.clone(),
                    })
                }
            }
            TokenType::OpenParens => {
                let expression = Self::parse_expression(token_iter)?;
                let closed_parens = Self::get_next_token_from_iter(token_iter)?;
                let TokenType::ClosedParens = closed_parens else {
                    return Err(anyhow!("Missing closed parentheses"));
                };
                Ok(expression)
            }
            TokenType::IntLiteral(constant) => Ok(Self::Constant {
                constant: *constant,
            }),
            TokenType::Minus | TokenType::BitwiseComplement | TokenType::LogicalNegation => {
                let nested_expression = Self::parse_factor(token_iter)?;
                let operator = Operator::get_unary_op_from_token(token)?;
                Ok(Self::UnaryOp {
                    operator,
                    factor: Box::new(nested_expression),
                })
            }
            _ => Err(anyhow!("Could not parse factor")),
        }
    }

    fn get_next_token_from_iter<'a>(
        token_iter: &mut PeekNth<Iter<'a, TokenType>>,
    ) -> anyhow::Result<&'a TokenType> {
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
        let function: anyhow::Result<AstNode> =
            AstNode::parse_factor(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            function.unwrap(),
            AstNode::FunctionCall {
                function_name: "main".into(),
                parameters: vec![
                    AstNode::Constant { constant: 1 },
                    AstNode::Constant { constant: 2 },
                    AstNode::Constant { constant: 3 },
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
            TokenType::Or,
            TokenType::IntLiteral(0),
        ];
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            exp.unwrap(),
            AstNode::BinaryOp {
                operator: Operator::Or,
                expression: Box::new(AstNode::BinaryOp {
                    operator: Operator::Equal,
                    expression: Box::new(AstNode::Constant { constant: 2 }),
                    next_expression: Box::new(AstNode::Constant { constant: 2 }),
                }),
                next_expression: Box::new(AstNode::Constant { constant: 0 }),
            }
        )
    }

    #[test]
    fn test_parse_binary_op_and_or() {
        let token_vec = vec![
            TokenType::IntLiteral(1),
            TokenType::Or,
            TokenType::IntLiteral(2),
            TokenType::And,
            TokenType::IntLiteral(3),
        ];
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            exp.unwrap(),
            AstNode::BinaryOp {
                operator: Operator::Or,
                expression: Box::new(AstNode::Constant { constant: 1 }),
                next_expression: Box::new(AstNode::BinaryOp {
                    operator: Operator::And,
                    expression: Box::new(AstNode::Constant { constant: 2 }),
                    next_expression: Box::new(AstNode::Constant { constant: 3 }),
                }),
            }
        )
    }

    #[test]
    fn test_parse_binary_op_subtraction() {
        let token_vec = vec![
            TokenType::IntLiteral(1),
            TokenType::Minus,
            TokenType::IntLiteral(2),
        ];
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            exp.unwrap(),
            AstNode::BinaryOp {
                operator: Operator::Subtraction,
                expression: Box::new(AstNode::Constant { constant: 1 }),
                next_expression: Box::new(AstNode::Constant { constant: 2 }),
            },
        )
    }

    #[test]
    fn test_parse_binary_op_multiplication() {
        let token_vec = vec![
            TokenType::IntLiteral(1),
            TokenType::Multiplication,
            TokenType::IntLiteral(2),
        ];
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            exp.unwrap(),
            AstNode::BinaryOp {
                operator: Operator::Multiplication,
                expression: Box::new(AstNode::Constant { constant: 1 }),
                next_expression: Box::new(AstNode::Constant { constant: 2 }),
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
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            exp.unwrap(),
            AstNode::BinaryOp {
                operator: Operator::Addition,
                expression: Box::new(AstNode::Constant { constant: 1 }),
                next_expression: Box::new(AstNode::BinaryOp {
                    operator: Operator::Multiplication,
                    expression: Box::new(AstNode::Constant { constant: 2 }),
                    next_expression: Box::new(AstNode::Constant { constant: 3 }),
                }),
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
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            exp.unwrap(),
            AstNode::BinaryOp {
                operator: Operator::Multiplication,
                expression: Box::new(AstNode::BinaryOp {
                    operator: Operator::Addition,
                    expression: Box::new(AstNode::Constant { constant: 1 }),
                    next_expression: Box::new(AstNode::Constant { constant: 2 }),
                }),
                next_expression: Box::new(AstNode::Constant { constant: 3 }),
            },
        )
    }

    #[test]
    fn test_parse_unary_op() {
        let token_vec = vec![TokenType::BitwiseComplement, TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
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
        let token_vec = vec![
            TokenType::BitwiseComplement,
            TokenType::BitwiseComplement,
            TokenType::IntLiteral(2),
        ];
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            exp.unwrap(),
            AstNode::UnaryOp {
                operator: Operator::BitwiseComplement,
                factor: Box::new(AstNode::UnaryOp {
                    operator: Operator::BitwiseComplement,
                    factor: Box::new(AstNode::Constant { constant: 2 }),
                },),
            }
        );
    }

    #[test]
    fn test_parse_ternary_operator() {
        let token_vec = vec![
            TokenType::IntLiteral(1),
            TokenType::QuestionMark,
            TokenType::IntLiteral(2),
            TokenType::Colon,
            TokenType::IntLiteral(3),
        ];
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            exp.unwrap(),
            AstNode::Conditional {
                condition: Box::new(AstNode::Constant { constant: 1 }),
                if_expression: Box::new(AstNode::Constant { constant: 2 }),
                else_expression: Box::new(AstNode::Constant { constant: 3 }),
            },
        );
    }

    #[test]
    fn test_parse_constant() {
        let token_vec = vec![TokenType::IntLiteral(2)];
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(exp.unwrap(), AstNode::Constant { constant: 2 });
    }

    #[test]
    fn test_parse_local_variable() {
        let token_vec = vec![TokenType::Identifier("a".into())];
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            exp.unwrap(),
            AstNode::Variable {
                variable: "a".into()
            }
        );
    }

    #[test]
    fn test_parse_assignment() {
        let token_vec = vec![
            TokenType::Identifier("a".into()),
            TokenType::Assignment,
            TokenType::IntLiteral(2),
        ];
        let exp: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            exp.unwrap(),
            AstNode::Assign {
                variable: "a".into(),
                expression: Box::new(AstNode::Constant { constant: 2 })
            }
        );
    }

    #[test]
    fn test_parse_statement() {
        let token_vec = vec![
            TokenType::Keyword("return".into()),
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
        ];
        let statement: anyhow::Result<AstNode> =
            AstNode::parse_statement(&mut peek_nth(token_vec.iter()));
        let expression = Box::new(AstNode::Constant { constant: 2 });
        assert_eq!(statement.unwrap(), AstNode::Return { expression });
    }

    #[test]
    fn test_parse_if_no_body() {
        let token_vec = vec![
            TokenType::Keyword("if".into()),
            TokenType::OpenParens,
            TokenType::Identifier("a".into()),
            TokenType::Equal,
            TokenType::IntLiteral(2),
            TokenType::ClosedParens,
            TokenType::Keyword("return".into()),
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
        ];
        let statement: anyhow::Result<AstNode> =
            AstNode::parse_statement(&mut peek_nth(token_vec.iter()));
        let condition = AstNode::BinaryOp {
            operator: Operator::Equal,
            expression: Box::new(AstNode::Variable {
                variable: "a".into(),
            }),
            next_expression: Box::new(AstNode::Constant { constant: 2 }),
        };
        let if_statement = AstNode::Return {
            expression: Box::new(AstNode::Constant { constant: 2 }),
        };
        assert_eq!(
            statement.unwrap(),
            AstNode::If {
                condition: Box::new(condition),
                if_statement: Box::new(if_statement),
                else_statement: None
            }
        );
    }

    #[test]
    fn test_parse_for_loop_expression() {
        let token_vec = vec![
            TokenType::Keyword("for".into()),
            TokenType::OpenParens,
            TokenType::Identifier("a".into()),
            TokenType::Assignment,
            TokenType::IntLiteral(0),
            TokenType::Semicolon,
            TokenType::Identifier("a".into()),
            TokenType::LessThan,
            TokenType::IntLiteral(5),
            TokenType::Semicolon,
            TokenType::Identifier("a".into()),
            TokenType::Assignment,
            TokenType::Identifier("a".into()),
            TokenType::Addition,
            TokenType::IntLiteral(1),
            TokenType::ClosedParens,
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
        ];
        let statement: anyhow::Result<AstNode> =
            AstNode::parse_statement(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            statement.unwrap(),
            AstNode::For {
                initial_decl_or_exp: Box::new(AstNode::Assign {
                    variable: "a".into(),
                    expression: Box::new(AstNode::Constant { constant: 0 })
                }),
                condition: Box::new(AstNode::BinaryOp {
                    operator: Operator::LessThan,
                    expression: Box::new(AstNode::Variable {
                        variable: "a".into()
                    }),
                    next_expression: Box::new(AstNode::Constant { constant: 5 })
                }),
                post_condition: Box::new(AstNode::Assign {
                    variable: "a".into(),
                    expression: Box::new(AstNode::BinaryOp {
                        operator: Operator::Addition,
                        expression: Box::new(AstNode::Variable {
                            variable: "a".into()
                        }),
                        next_expression: Box::new(AstNode::Constant { constant: 1 })
                    })
                }),
                body: Box::new(AstNode::Constant { constant: 2 })
            }
        );
    }

    #[test]
    fn test_parse_for_loop_declaration() {
        let token_vec = vec![
            TokenType::Keyword("for".into()),
            TokenType::OpenParens,
            TokenType::Keyword("int".into()),
            TokenType::Identifier("a".into()),
            TokenType::Assignment,
            TokenType::IntLiteral(0),
            TokenType::Semicolon,
            TokenType::Identifier("a".into()),
            TokenType::LessThan,
            TokenType::IntLiteral(5),
            TokenType::Semicolon,
            TokenType::Identifier("a".into()),
            TokenType::Assignment,
            TokenType::Identifier("a".into()),
            TokenType::Addition,
            TokenType::IntLiteral(1),
            TokenType::ClosedParens,
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
        ];
        let statement: anyhow::Result<AstNode> =
            AstNode::parse_statement(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            statement.unwrap(),
            AstNode::For {
                initial_decl_or_exp: Box::new(AstNode::Declare {
                    variable: "a".into(),
                    expression: Some(Box::new(AstNode::Constant { constant: 0 }))
                }),
                condition: Box::new(AstNode::BinaryOp {
                    operator: Operator::LessThan,
                    expression: Box::new(AstNode::Variable {
                        variable: "a".into()
                    }),
                    next_expression: Box::new(AstNode::Constant { constant: 5 })
                }),
                post_condition: Box::new(AstNode::Assign {
                    variable: "a".into(),
                    expression: Box::new(AstNode::BinaryOp {
                        operator: Operator::Addition,
                        expression: Box::new(AstNode::Variable {
                            variable: "a".into()
                        }),
                        next_expression: Box::new(AstNode::Constant { constant: 1 })
                    })
                }),
                body: Box::new(AstNode::Constant { constant: 2 })
            }
        );
    }

    #[test]
    fn test_parse_for_loop_null_expressions() {
        let token_vec = vec![
            TokenType::Keyword("for".into()),
            TokenType::OpenParens,
            TokenType::Semicolon,
            TokenType::Semicolon,
            TokenType::ClosedParens,
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
        ];
        let statement: anyhow::Result<AstNode> =
            AstNode::parse_statement(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            statement.unwrap(),
            AstNode::For {
                initial_decl_or_exp: Box::new(AstNode::NullExpression),
                condition: Box::new(AstNode::NullExpression),
                post_condition: Box::new(AstNode::NullExpression),
                body: Box::new(AstNode::Constant { constant: 2 })
            }
        );
    }

    #[test]
    fn test_parse_while_loop() {
        let token_vec = vec![
            TokenType::Keyword("while".into()),
            TokenType::OpenParens,
            TokenType::Identifier("a".into()),
            TokenType::LessThan,
            TokenType::IntLiteral(5),
            TokenType::ClosedParens,
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
        ];
        let statement: anyhow::Result<AstNode> =
            AstNode::parse_statement(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            statement.unwrap(),
            AstNode::While {
                condition: Box::new(AstNode::BinaryOp {
                    operator: Operator::LessThan,
                    expression: Box::new(AstNode::Variable {
                        variable: "a".into()
                    }),
                    next_expression: Box::new(AstNode::Constant { constant: 5 })
                }),
                body: Box::new(AstNode::Constant { constant: 2 })
            }
        );
    }

    #[test]
    fn test_parse_do_loop() {
        let token_vec = vec![
            TokenType::Keyword("do".into()),
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
            TokenType::Keyword("while".into()),
            TokenType::OpenParens,
            TokenType::Identifier("a".into()),
            TokenType::LessThan,
            TokenType::IntLiteral(5),
            TokenType::ClosedParens,
            TokenType::Semicolon,
        ];
        let statement: anyhow::Result<AstNode> =
            AstNode::parse_statement(&mut peek_nth(token_vec.iter()));
        assert_eq!(
            statement.unwrap(),
            AstNode::Do {
                body: Box::new(AstNode::Constant { constant: 2 }),
                condition: Box::new(AstNode::BinaryOp {
                    operator: Operator::LessThan,
                    expression: Box::new(AstNode::Variable {
                        variable: "a".into()
                    }),
                    next_expression: Box::new(AstNode::Constant { constant: 5 })
                }),
            }
        );
    }

    #[test]
    fn test_parse_declaration() {
        let token_vec = vec![
            TokenType::Keyword("int".into()),
            TokenType::Identifier("a".into()),
            TokenType::Assignment,
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
        ];
        let statement: anyhow::Result<AstNode> =
            AstNode::parse_block_item(&mut peek_nth(token_vec.iter()));
        let expression = Box::new(AstNode::Constant { constant: 2 });
        assert_eq!(
            statement.unwrap(),
            AstNode::Declare {
                variable: "a".into(),
                expression: Some(expression)
            }
        );
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
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
            TokenType::ClosedBrace,
        ];
        let function: anyhow::Result<AstNode> =
            AstNode::parse_function(&mut peek_nth(token_vec.iter()));
        let expression = Box::new(AstNode::Constant { constant: 2 });
        let statement = AstNode::Return { expression };
        assert_eq!(
            function.unwrap(),
            AstNode::Function {
                function_name: "main".into(),
                parameters: vec!["param1".into(), "param2".into(), "param3".into()],
                body: Some(Box::new(AstNode::Compound {
                    block_item_list: vec![statement]
                }))
            }
        );
    }

    #[test]
    fn test_parse_program_multiple_func() {
        let token_vec = vec![
            // first function declaration
            TokenType::Keyword("int".into()),
            TokenType::Identifier("helper".into()),
            TokenType::OpenParens,
            TokenType::Identifier("param1".into()),
            TokenType::Identifier("param2".into()),
            TokenType::Identifier("param3".into()),
            TokenType::ClosedParens,
            TokenType::Semicolon,
            // main function definition
            TokenType::Keyword("int".into()),
            TokenType::Identifier("main".into()),
            TokenType::OpenParens,
            TokenType::ClosedParens,
            TokenType::OpenBrace,
            TokenType::Keyword("return".into()),
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
            TokenType::ClosedBrace,
        ];

        let program: anyhow::Result<AstNode> = AstNode::parse(&token_vec);
        assert_eq!(
            program.unwrap(),
            AstNode::Program {
                function_list: vec![
                    AstNode::Function {
                        function_name: "helper".into(),
                        parameters: vec!["param1".into(), "param2".into(), "param3".into(),],
                        body: None,
                    },
                    AstNode::Function {
                        function_name: "main".into(),
                        parameters: vec![],
                        body: Some(Box::new(AstNode::Compound {
                            block_item_list: vec![AstNode::Return {
                                expression: Box::new(AstNode::Constant { constant: 2 }),
                            }]
                        }))
                    },
                ]
            }
        );
    }

    #[test]
    fn test_parse_function_multiple_statements() {
        let token_vec = vec![
            TokenType::Keyword("int".into()),
            TokenType::Identifier("main".into()),
            TokenType::OpenParens,
            TokenType::Identifier("param1".into()),
            TokenType::Identifier("param2".into()),
            TokenType::Identifier("param3".into()),
            TokenType::ClosedParens,
            TokenType::OpenBrace,
            TokenType::Identifier("a".into()),
            TokenType::Equal,
            TokenType::IntLiteral(1),
            TokenType::Semicolon,
            TokenType::Keyword("return".into()),
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
            TokenType::ClosedBrace,
        ];
        let function: anyhow::Result<AstNode> =
            AstNode::parse_function(&mut peek_nth(token_vec.iter()));
        let expression = Box::new(AstNode::Constant { constant: 2 });
        let statement_1 = AstNode::BinaryOp {
            operator: Operator::Equal,
            expression: Box::new(AstNode::Variable {
                variable: "a".into(),
            }),
            next_expression: Box::new(AstNode::Constant { constant: 1 }),
        };
        let statement_2 = AstNode::Return { expression };
        assert_eq!(
            function.unwrap(),
            AstNode::Function {
                function_name: "main".into(),
                parameters: vec!["param1".into(), "param2".into(), "param3".into()],
                body: Some(Box::new(AstNode::Compound {
                    block_item_list: vec![statement_1, statement_2]
                }))
            }
        );
    }

    #[test]
    fn test_parse_if_compound_statements() {
        let token_vec = vec![
            TokenType::Keyword("if".into()),
            TokenType::OpenParens,
            TokenType::Identifier("a".into()),
            TokenType::Equal,
            TokenType::IntLiteral(2),
            TokenType::ClosedParens,
            TokenType::OpenBrace,
            TokenType::Identifier("a".into()),
            TokenType::Equal,
            TokenType::IntLiteral(1),
            TokenType::Semicolon,
            TokenType::Keyword("return".into()),
            TokenType::IntLiteral(2),
            TokenType::Semicolon,
            TokenType::ClosedBrace,
        ];
        let statement: anyhow::Result<AstNode> =
            AstNode::parse_statement(&mut peek_nth(token_vec.iter()));
        let condition = AstNode::BinaryOp {
            operator: Operator::Equal,
            expression: Box::new(AstNode::Variable {
                variable: "a".into(),
            }),
            next_expression: Box::new(AstNode::Constant { constant: 2 }),
        };
        let nested_statement_1 = AstNode::BinaryOp {
            operator: Operator::Equal,
            expression: Box::new(AstNode::Variable {
                variable: "a".into(),
            }),
            next_expression: Box::new(AstNode::Constant { constant: 1 }),
        };
        let nested_statement_2 = AstNode::Return {
            expression: Box::new(AstNode::Constant { constant: 2 }),
        };
        let if_statement = AstNode::Compound {
            block_item_list: vec![nested_statement_1, nested_statement_2],
        };
        assert_eq!(
            statement.unwrap(),
            AstNode::If {
                condition: Box::new(condition),
                if_statement: Box::new(if_statement),
                else_statement: None
            }
        );
    }

    #[test]
    fn test_parse_null_expression() {
        let token_vec = vec![TokenType::Semicolon];
        let expression: anyhow::Result<AstNode> =
            AstNode::parse_expression(&mut peek_nth(token_vec.iter()));
        assert_eq!(expression.unwrap(), AstNode::NullExpression,);
    }

    #[test]
    fn test_parse_null_expression_invalid_statement() {
        let token_vec = vec![TokenType::ClosedParens];
        let statement: anyhow::Result<AstNode> =
            AstNode::parse_statement(&mut peek_nth(token_vec.iter()));
        assert!(statement.is_err_and(|e| e.to_string() == "Statement does not end in semicolon"));
    }
}
