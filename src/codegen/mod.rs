use anyhow::anyhow;
#[cfg(test)]
use assert_str::assert_str_trim_eq;

use crate::parser::{AstNode, Operator};

const INDENT: &str = "	";

pub struct Codegen {
    stack_offset_bytes: i32
}

impl Codegen {
    pub fn new() -> Self {
        Codegen { stack_offset_bytes: 0 }
    }

    pub fn codegen(&mut self, ast: AstNode) -> anyhow::Result<String> {
        let AstNode::Program{function} = ast else {
            return Err(anyhow!("Called codegen on node that is not a program"))
        };

        let mut result = String::new();

        // traverse the AST
        let generated_func = self.generate_function(*function)?;
        result.push_str(&generated_func);

        Ok(result)
    }

    fn format_instruction(instruction: &str, args: Vec<&str>) -> String {
        if args.len() > 0 {
            format!("{}{}{}{}\n", INDENT, instruction, INDENT, args.join(", "))
        } else {
            format!("{}{}\n", INDENT, instruction)
        }
    }

    fn generate_push_instruction(&mut self, register: &str) -> String {
        let mut result = String::new();
        // allocate more space if needed
        // sp pointer must be 16 byte aligned
        if self.stack_offset_bytes % 16 == 0 {
            result.push_str(&Self::format_instruction("sub", vec!["sp", "sp", "#16"]));
        }
        let offset = 16 - self.stack_offset_bytes % 16 - 4;  // TODO: update to support other register sizes
        result.push_str(&Self::format_instruction("str", vec![register, &format!("[sp, {}]", offset)]));
        self.stack_offset_bytes += 4;
        result
    }

    fn generate_pop_instruction(&mut self, register: &str) -> String {
        let mut result = String::new();
        let offset = (16 - self.stack_offset_bytes % 16) % 16;  // TODO: update to support other register sizes
        result.push_str(&Self::format_instruction("ldr", vec![register, &format!("[sp, {}]", offset)]));
        self.stack_offset_bytes -= 4;
        // free space if needed
        if self.stack_offset_bytes % 16 == 0 {
            result.push_str(&Self::format_instruction("add", vec!["sp", "sp", "16"]));
        };
        result
    }


    fn generate_function(&mut self, node: AstNode) -> anyhow::Result<String> {
        let AstNode::Function{identifier, statement} = node else {
            return Err(anyhow!("Called generate_function on node that is not a function"))
        };

        let mut result: String = String::new();

        result.push_str(&format!("{}.globl _{}\n", INDENT, identifier));
        result.push_str(&format!("_{}:\n", identifier));

        // generate statement
        let generated_statement = self.generate_statement(*statement)?;
        result.push_str(&generated_statement);

        Ok(result)
    }

    fn generate_statement(&mut self, node: AstNode) -> anyhow::Result<String> {
        let AstNode::Statement{expression} = node else {
            return Err(anyhow!("Called generate_statement on node that is not a statement"))
        };

        // only return statements supported for now
        let mut result: String = String::new();

        let generated_expression: String = self.generate_expression(*expression)?;
        result.push_str(&generated_expression);
        result.push_str(&Self::format_instruction("ret", vec![]));

        Ok(result)
    }

    fn generate_expression(&mut self, node: AstNode) -> anyhow::Result<String> {
        let mut result: String = String::new();

        match node {
            AstNode::Constant { constant } => {
                let constant_str = format!("#{}", constant);
                result.push_str(&Self::format_instruction("mov", vec!["w0", &constant_str[..]]));
            },
            AstNode::UnaryOp { operator, factor } => {
                let nested_expression = self.generate_expression(*factor)?;
                result.push_str(&nested_expression);
                // assume previous operation moves the value to w0
                match operator {
                    Operator::Negation => {
                        result.push_str(&Self::format_instruction("neg", vec!["w0", "w0"]));
                    },
                    Operator::BitwiseComplement => {
                        result.push_str(&Self::format_instruction("mvn", vec!["w0", "w0"]));  // logical nor with itself
                    },
                    Operator::LogicalNegation => {
                        result.push_str(&Self::format_instruction("cmp", vec!["w0", "#0"]));  // compare w0 to 0, setting flag
                        result.push_str(&Self::format_instruction("mov", vec!["w0", "#1"]));  // set w0 to 1 (doesn't clear flags)
                        result.push_str(&Self::format_instruction("csel", vec!["w0", "w0", "wzr", "EQ"]));  // select 1 if true else 0
                    }
                    _ => {
                        return Err(anyhow!("Not a unary operator"));
                    }
                }
            },
            AstNode::BinaryOp { operator, term, next_term } => {
                let nested_term_1 = self.generate_expression(*term)?;
                let nested_term_2 = self.generate_expression(*next_term)?;

                // write instructions for term 1
                result.push_str(&nested_term_1);
                // push w0 to stack
                result.push_str(&self.generate_push_instruction("w0"));

                // write code for term 2
                result.push_str(&nested_term_2);
                // pop term 1 from stack into w1
                result.push_str(&self.generate_pop_instruction("w1"));

                // operation, term 1, term 2
                match operator {
                    Operator::Addition => {},
                    Operator::Subtraction => {},
                    Operator::Multiplication => {},
                    Operator::Division => {},
                    _ => {}
                }
            }
            _ => {
                return Err(anyhow!("Malformed expression"));
            }
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use crate::codegen::Codegen;

    use super::*;

    #[test]
    fn test_codegen() {
        let expression = Box::new(AstNode::Constant { constant: 2 });
        let statement = Box::new(AstNode::Statement {expression});
        let function = Box::new(AstNode::Function {identifier: "main".into(), statement});
        let program = AstNode::Program{function};

        let mut codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        assert_str_trim_eq!(
            result, "
                .globl _main
                _main:
                    mov	w0, #2
                    ret
            "
        )
    }

    #[test]
    fn test_unary_op() {
        let constant = Box::new(AstNode::Constant { constant: 2 });
        let expression = Box::new(AstNode::UnaryOp { operator: Operator::BitwiseComplement, factor: constant });
        let statement = Box::new(AstNode::Statement {expression});
        let function = Box::new(AstNode::Function {identifier: "main".into(), statement});
        let program = AstNode::Program{function};

        let mut codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        assert_str_trim_eq!(
            result, "
                .globl _main
                _main:
                    mov	w0, #2
                    mvn	w0, w0
                    ret
            "
        )
    }

    #[test]
    fn test_stack_push_pop() {
        let mut codegen: Codegen = Codegen::new();
        let mut result = String::new();

        result.push_str(&codegen.generate_push_instruction("w0"));
        assert_eq!(codegen.stack_offset_bytes, 4);
        result.push_str(&codegen.generate_push_instruction("w1"));
        assert_eq!(codegen.stack_offset_bytes, 8);
        result.push_str(&codegen.generate_push_instruction("w2"));
        assert_eq!(codegen.stack_offset_bytes, 12);
        result.push_str(&codegen.generate_push_instruction("w3"));
        assert_eq!(codegen.stack_offset_bytes, 16);
        result.push_str(&codegen.generate_push_instruction("w4"));
        assert_eq!(codegen.stack_offset_bytes, 20);

        result.push_str(&&codegen.generate_pop_instruction("w0"));
        result.push_str(&&codegen.generate_pop_instruction("w1"));
        result.push_str(&&codegen.generate_pop_instruction("w2"));
        result.push_str(&&codegen.generate_pop_instruction("w3"));
        result.push_str(&&codegen.generate_pop_instruction("w4"));
        assert_eq!(codegen.stack_offset_bytes, 0);

        assert_str_trim_eq!(
            result, "
                    sub	sp, sp, #16
                    str	w0, [sp, 12]
                    str	w1, [sp, 8]
                    str	w2, [sp, 4]
                    str	w3, [sp, 0]
                    sub	sp, sp, #16
                    str	w4, [sp, 12]
                    ldr	w0, [sp, 12]
                    add	sp, sp, 16
                    ldr	w1, [sp, 0]
                    ldr	w2, [sp, 4]
                    ldr	w3, [sp, 8]
                    ldr	w4, [sp, 12]
                    add	sp, sp, 16
            "
        )
    }

    #[test]
    fn test_binary_op() {
        let constant_1 = Box::new(AstNode::Constant { constant: 1 });
        let constant_2 = Box::new(AstNode::Constant { constant: 2 });
        let expression = Box::new(AstNode::BinaryOp { operator: Operator::Addition, term: constant_1, next_term: constant_2 });
        let statement = Box::new(AstNode::Statement {expression});
        let function = Box::new(AstNode::Function {identifier: "main".into(), statement});
        let program = AstNode::Program{function};

        let mut codegen: Codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        assert_str_trim_eq!(
            result, "
                .globl _main
                _main:
                    mov	w0, #1
                    sub	sp, sp, #16
                    str	w0, [sp, 12]
                    mov	w0, #2
                    ldr	w1, [sp, 12]
                    add	sp, sp, 16
                    ret
            "
        )
    }
}