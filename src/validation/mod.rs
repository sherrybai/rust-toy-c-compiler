use std::collections::{HashMap, HashSet};

use crate::parser::AstNode;

use anyhow::anyhow;

pub struct Validation {
    function_name_to_arg_count: HashMap<String, usize>,
    function_is_defined: HashSet<String>,
}

impl Validation {
    pub fn new() -> Self {
        Validation {
            function_name_to_arg_count: HashMap::new(),
            function_is_defined: HashSet::new(),
        }
    }

    pub fn validate_ast(&mut self, ast: &AstNode) -> anyhow::Result<()> {
        let AstNode::Program { function_list } = ast else {
            return Err(anyhow!("Called validate_ast on node that is not a program"));
        };

        // track function declarations/definitions
        for function in function_list {
            let AstNode::Function {
                ref function_name,
                ref parameters,
                body: ref statement,
            } = function
            else {
                return Err(anyhow!("Program function list contains non-function"));
            };

            match statement {
                None => {
                    // function declaration
                    // cannot have two function declarations with same name, different number of params
                    if let Some(param_count) = self.function_name_to_arg_count.get(function_name) {
                        if parameters.len() != *param_count {
                            return Err(anyhow!(
                                "Found duplicate function declarations with different param counts"
                            ));
                        }
                    }
                    self.function_name_to_arg_count
                        .insert(function_name.clone(), parameters.len());
                }
                Some(statement_node) => {
                    // function definition
                    // cannot have two function definitions
                    if self.function_is_defined.contains(function_name) {
                        return Err(anyhow!("Found duplicate function definitions"));
                    }
                    if let Some(param_count) = self.function_name_to_arg_count.get(function_name) {
                        // cannot have definition with different number of params as declaration
                        if parameters.len() != *param_count {
                            return Err(anyhow!(
                                "Defined and declared functions have different number of arguments"
                            ));
                        }
                    } else {
                        // function declared and defined at the same time
                        self.function_name_to_arg_count
                            .insert(function_name.clone(), parameters.len());
                    }
                    self.function_is_defined.insert(function_name.clone());

                    // traverse function to validate expressions
                    self.validate_block_item(statement_node)?;
                }
            }
        }

        Ok(())
    }

    fn validate_block_item(&mut self, node: &AstNode) -> anyhow::Result<()> {
        match node {
            AstNode::Return { ref expression } => {
                self.validate_expression(expression)?;
            }
            AstNode::Declare {
                variable: _,
                ref expression,
            } => {
                if let Some(exp) = expression {
                    self.validate_expression(exp)?;
                }
            }
            AstNode::If {
                condition,
                if_statement,
                else_statement,
            } => {
                self.validate_expression(condition)?;
                self.validate_block_item(if_statement)?;
                if let Some(statement) = else_statement {
                    self.validate_block_item(statement)?;
                }
            }
            AstNode::For {
                initial_decl_or_exp,
                condition,
                post_condition,
                body,
            } => {
                match **initial_decl_or_exp {
                    AstNode::Declare {
                        variable: _,
                        ref expression,
                    } => {
                        if let Some(exp) = expression {
                            self.validate_expression(exp)?;
                        }
                    }
                    _ => {
                        self.validate_expression(initial_decl_or_exp)?;
                    }
                }
                self.validate_expression(condition)?;
                self.validate_expression(post_condition)?;
                self.validate_block_item(body)?;
            }
            AstNode::While { condition, body } => {
                self.validate_block_item(body)?;
                self.validate_expression(condition)?;
            }
            AstNode::Do { body, condition } => {
                self.validate_expression(condition)?;
                self.validate_block_item(body)?;
            }
            AstNode::Compound { block_item_list } => {
                for block_item in block_item_list {
                    self.validate_block_item(block_item)?;
                }
            }
            _ => {
                self.validate_expression(node)?;
            }
        }
        Ok(())
    }

    fn validate_expression(&mut self, node: &AstNode) -> anyhow::Result<()> {
        // recursively call into nested expressions
        match node {
            AstNode::FunctionCall {
                ref function_name,
                ref parameters,
            } => {
                // cannot call function with wrong number of args
                if let Some(param_count) = self.function_name_to_arg_count.get(function_name) {
                    if parameters.len() != *param_count {
                        return Err(anyhow!(
                            "Called function with incorrect number of arguments"
                        ));
                    }
                } else {
                    // function called before it is declared
                    return Err(anyhow!("Called function before it has been declared"));
                }
            }
            AstNode::BinaryOp {
                operator: _,
                expression,
                next_expression,
            } => {
                self.validate_expression(expression)?;
                self.validate_expression(next_expression)?;
            }
            AstNode::UnaryOp {
                operator: _,
                factor,
            } => {
                self.validate_expression(factor)?;
            }
            AstNode::Assign {
                variable: _,
                expression,
            } => {
                self.validate_expression(expression)?;
            }
            AstNode::Conditional {
                condition,
                if_expression,
                else_expression,
            } => {
                self.validate_expression(condition)?;
                self.validate_expression(if_expression)?;
                self.validate_expression(else_expression)?;
            }
            AstNode::Break => {
                // do nothing
            }
            AstNode::Continue => {
                // do nothing
            }
            AstNode::Variable { variable: _ } => {
                // do nothing
            }
            AstNode::Constant { constant: _ } => {
                // do nothing
            }
            AstNode::NullExpression => {
                // do nothing
            }
            _ => {
                println!("{:?}", node);
                return Err(anyhow!("Invalid expression node variant"));
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::validation::Validation;

    use super::*;

    #[test]
    fn test_valid_main() {
        let expression = Box::new(AstNode::Constant { constant: 2 });
        let statement = AstNode::Return { expression };
        let function = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            body: Some(Box::new(AstNode::Compound {
                block_item_list: vec![statement],
            })),
        };
        let program = AstNode::Program {
            function_list: vec![function],
        };

        let mut validation = Validation::new();
        // no error thrown
        assert!(validation.validate_ast(&program).is_ok());
    }

    #[test]
    fn test_duplicate_definition() {
        let function_1 = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            body: Some(Box::new(AstNode::Compound {
                block_item_list: vec![AstNode::Return {
                    expression: Box::new(AstNode::Constant { constant: 1 }),
                }],
            })),
        };
        let function_2 = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            body: Some(Box::new(AstNode::Compound {
                block_item_list: vec![AstNode::Return {
                    expression: Box::new(AstNode::Constant { constant: 2 }),
                }],
            })),
        };
        let program = AstNode::Program {
            function_list: vec![function_1, function_2],
        };

        let mut validation = Validation::new();
        // duplicate definition error
        assert!(validation
            .validate_ast(&program)
            .is_err_and(|e| e.to_string() == "Found duplicate function definitions"));
    }

    #[test]
    fn test_different_arg_count_declarations() {
        let declaration_1 = AstNode::Function {
            function_name: "main".into(),
            parameters: vec!["a".into(), "b".into()],
            body: None,
        };
        let declaration_2 = AstNode::Function {
            function_name: "main".into(),
            parameters: vec!["a".into()],
            body: None,
        };
        let program = AstNode::Program {
            function_list: vec![declaration_1, declaration_2],
        };

        let mut validation = Validation::new();
        // different number of arguments
        assert!(validation
            .validate_ast(&program)
            .is_err_and(|e| e.to_string()
                == "Found duplicate function declarations with different param counts"));
    }

    #[test]
    fn test_different_arg_count_definition_declaration() {
        let declaration = AstNode::Function {
            function_name: "main".into(),
            parameters: vec!["a".into(), "b".into()],
            body: None,
        };
        let definition = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            body: Some(Box::new(AstNode::Compound {
                block_item_list: vec![AstNode::Return {
                    expression: Box::new(AstNode::Constant { constant: 2 }),
                }],
            })),
        };
        let program = AstNode::Program {
            function_list: vec![declaration, definition],
        };

        let mut validation = Validation::new();
        // different number of arguments
        assert!(validation
            .validate_ast(&program)
            .is_err_and(|e| e.to_string()
                == "Defined and declared functions have different number of arguments"));
    }

    #[test]
    fn test_function_call_not_declared() {
        let function_1 = AstNode::Function {
            function_name: "helper".into(),
            parameters: vec![],
            body: None,
        };
        let function_2 = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            body: Some(Box::new(AstNode::Compound {
                block_item_list: vec![AstNode::Return {
                    expression: Box::new(AstNode::FunctionCall {
                        function_name: "helper".into(),
                        parameters: vec![],
                    }),
                }],
            })),
        };
        // helper function declared after main
        let program = AstNode::Program {
            function_list: vec![function_2, function_1],
        };

        let mut validation = Validation::new();
        assert!(validation
            .validate_ast(&program)
            .is_err_and(|e| e.to_string() == "Called function before it has been declared"));
    }

    #[test]
    fn test_function_call_wrong_arg_count() {
        let function_1 = AstNode::Function {
            function_name: "helper".into(),
            parameters: vec!["a".into(), "b".into()],
            body: None,
        };
        let function_2 = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            body: Some(Box::new(AstNode::Compound {
                block_item_list: vec![AstNode::Return {
                    expression: Box::new(AstNode::FunctionCall {
                        function_name: "helper".into(),
                        parameters: vec![],
                    }),
                }],
            })),
        };
        let program = AstNode::Program {
            function_list: vec![function_1, function_2],
        };

        let mut validation = Validation::new();
        // different number of arguments
        assert!(validation
            .validate_ast(&program)
            .is_err_and(|e| e.to_string() == "Called function with incorrect number of arguments"));
    }
}
