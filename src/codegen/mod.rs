use std::collections::HashMap;

use anyhow::anyhow;
#[cfg(test)]
use assert_str::assert_str_trim_eq;

use crate::parser::{AstNode, Operator};

const INDENT: &str = "	";

pub struct Codegen {
    stack_offset_bytes: i32,
    label_counter: u32,
    variable_map: HashMap<String, i32>,
}

impl Codegen {
    pub fn new() -> Self {
        Codegen {
            stack_offset_bytes: 0,
            label_counter: 1,
            variable_map: HashMap::new(),
        }
    }

    pub fn codegen(&mut self, ast: AstNode) -> anyhow::Result<String> {
        let AstNode::Program { function_list } = ast else {
            return Err(anyhow!("Called codegen on node that is not a program"));
        };

        let mut result: String = String::new();

        // traverse the AST
        for function in function_list.iter() {
            let generated_func = self.generate_function(function)?;
            result.push_str(&generated_func);
        }

        Ok(result)
    }

    fn format_instruction(instruction: &str, args: Vec<&str>) -> String {
        if !args.is_empty() {
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
        let offset = 16 + self.stack_offset_bytes % 16 - 4; // TODO: update to support other register sizes
        result.push_str(&Self::format_instruction(
            "str",
            vec![register, &format!("[sp, {}]", offset)],
        ));
        self.stack_offset_bytes -= 4;
        result
    }

    fn generate_pop_instruction(&mut self, register: &str) -> String {
        let mut result = String::new();
        let offset = (16 + self.stack_offset_bytes % 16) % 16; // TODO: update to support other register sizes
        result.push_str(&Self::format_instruction(
            "ldr",
            vec![register, &format!("[sp, {}]", offset)],
        ));
        self.stack_offset_bytes += 4;
        // free space if needed
        if self.stack_offset_bytes % 16 == 0 {
            result.push_str(&Self::format_instruction("add", vec!["sp", "sp", "16"]));
        };
        result
    }

    fn generate_variable_assignment(&mut self, stack_offset_bytes: i32) -> String {
        // overwrite value at stack offset location
        let mut result = String::new();
        // use stack offset bytes to find absolute location in the stack
        let stack_pointer_offset = (-self.stack_offset_bytes + 12) / 16 * 16; // take next highest 16 byte value
        let offset = stack_pointer_offset + stack_offset_bytes; // TODO: update to support other register sizes
        result.push_str(&Self::format_instruction(
            "str",
            vec!["w0", &format!("[sp, {}]", offset)],
        ));
        result
    }

    fn generate_variable_read(&mut self, stack_offset_bytes: i32) -> String {
        // overwrite value at stack offset location
        let mut result = String::new();
        // use stack offset bytes to find absolute location in the stack
        let stack_pointer_offset = (-self.stack_offset_bytes + 12) / 16 * 16; // take next highest 16 byte value
        let offset = stack_pointer_offset + stack_offset_bytes; // TODO: update to support other register sizes
        result.push_str(&Self::format_instruction(
            "ldr",
            vec!["w0", &format!("[sp, {}]", offset)],
        ));
        result
    }

    fn generate_function_prologue() -> String {
        let mut result = String::new();
        // write frame pointer and link register (return address) to stack
        // stack pointer remains 16 byte aligned
        result.push_str(&Self::format_instruction(
            "stp",
            vec!["x29", "x30", "[sp, -16]!"],
        ));
        // stack pointer now points to frame pointer (top of the caller function’s stack frame)
        // top of caller's stack frame is bottom of callee's stack frame
        result.push_str(&Self::format_instruction("mov", vec!["x29", "sp"]));
        result
    }

    fn generate_function_epilogue(&mut self) -> String {
        let mut result = String::new();

        // need to restore stack pointer
        let stack_pointer_offset = (-self.stack_offset_bytes + 12) / 16 * 16; // take next highest 16 byte value
        if stack_pointer_offset != 0 {
            result.push_str(&Self::format_instruction(
                "add",
                vec!["sp", "sp", &format!("{}", stack_pointer_offset)[..]],
            ));
        }
        // read frame pointer and link register (return address) from stack
        // stack pointer remains 16 byte aligned
        result.push_str(&Self::format_instruction(
            "ldp",
            vec!["x29", "x30", "[sp]", "16"],
        ));

        result
    }

    fn generate_function(&mut self, node: &AstNode) -> anyhow::Result<String> {
        let AstNode::Function {
            function_name,
            parameters,
            statement_list,
        } = node
        else {
            return Err(anyhow!(
                "Called generate_function on node that is not a function"
            ));
        };

        let mut result: String = String::new();
        let mut explicit_return: bool = false;
        if let Some(s) = statement_list {
            // only generate assembly for function node if it is a definition
            // (non-null function body)

            // function definition
            result.push_str(&format!("{}.globl _{}\n", INDENT, function_name));
            result.push_str(&format!("_{}:\n", function_name));

            // set up stack frame
            result.push_str(&Self::generate_function_prologue());

            for statement in s {
                let generated_statement = self.generate_statement(statement)?;
                result.push_str(&generated_statement);

                if let AstNode::Return { expression: _ } = statement {
                    explicit_return = true;
                    break; // don't bother generating code after return
                }
            }
            if !explicit_return {
                // return 0
                result.push_str(&Self::format_instruction("mov", vec!["w0", "0"]));
            }

            result.push_str(&self.generate_function_epilogue());
            result.push_str(&Self::format_instruction("ret", vec![]));
        }

        Ok(result)
    }

    fn generate_statement(&mut self, node: &AstNode) -> anyhow::Result<String> {
        let mut result: String = String::new();

        match node {
            AstNode::Return { expression } => {
                let generated_expression: String = self.generate_expression(expression)?;
                result.push_str(&generated_expression);
                // write return later
            }
            AstNode::Declare {
                variable,
                expression,
            } => {
                if self.variable_map.contains_key(variable) {
                    return Err(anyhow!("Variable already declared"));
                }

                let generated_expression: String;
                if let Some(nested_expression) = expression {
                    // write expression
                    generated_expression = self.generate_expression(nested_expression)?;
                } else {
                    // initialize variable to 0
                    generated_expression = Self::format_instruction("mov", vec!["w0", "0"]);
                }
                result.push_str(&generated_expression);
                // assume value lives in w0
                // push onto stack
                result.push_str(&self.generate_push_instruction("w0"));
                self.variable_map
                    .insert(variable.clone(), self.stack_offset_bytes);
            }
            _ => {
                result.push_str(&self.generate_expression(node)?);
            }
        }
        Ok(result)
    }

    fn generate_expression(&mut self, node: &AstNode) -> anyhow::Result<String> {
        let mut result: String = String::new();

        match node {
            AstNode::Constant { constant } => {
                let constant_str = format!("#{}", constant);
                result.push_str(&Self::format_instruction(
                    "mov",
                    vec!["w0", &constant_str[..]],
                ));
            }
            AstNode::Variable { variable } => {
                if !self.variable_map.contains_key(variable) {
                    return Err(anyhow!("Variable not declared before assignment"));
                }
                let stack_offset = self.variable_map.get(variable).unwrap();
                result.push_str(&self.generate_variable_read(*stack_offset));
            }
            AstNode::UnaryOp { operator, factor } => {
                let nested_expression = self.generate_expression(factor)?;
                result.push_str(&nested_expression);
                // assume previous operation moves the value to w0
                match operator {
                    Operator::Negation => {
                        result.push_str(&Self::format_instruction("neg", vec!["w0", "w0"]));
                    }
                    Operator::BitwiseComplement => {
                        result.push_str(&Self::format_instruction("mvn", vec!["w0", "w0"]));
                        // logical nor with itself
                    }
                    Operator::LogicalNegation => {
                        result.push_str(&Self::format_instruction("cmp", vec!["w0", "#0"])); // compare w0 to 0, setting flag
                        result.push_str(&Self::format_instruction("mov", vec!["w0", "#1"])); // set w0 to 1 (doesn't clear flags)
                        result.push_str(&Self::format_instruction(
                            "csel",
                            vec!["w0", "w0", "wzr", "EQ"],
                        )); // select 1 if true else 0
                    }
                    _ => {
                        return Err(anyhow!("Not a unary operator"));
                    }
                }
            }
            AstNode::BinaryOp {
                operator,
                expression: term,
                next_expression: next_term,
            } => {
                let nested_term_1 = self.generate_expression(term)?;
                let nested_term_2 = self.generate_expression(next_term)?;

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
                    Operator::Addition => {
                        result.push_str(&Self::format_instruction("add", vec!["w0", "w1", "w0"]));
                    }
                    Operator::Subtraction => {
                        result.push_str(&Self::format_instruction("sub", vec!["w0", "w1", "w0"]));
                    }
                    Operator::Multiplication => {
                        result.push_str(&Self::format_instruction("mul", vec!["w0", "w1", "w0"]));
                    }
                    Operator::Division => {
                        result.push_str(&Self::format_instruction("sdiv", vec!["w0", "w1", "w0"]));
                    }
                    Operator::AND => {
                        let label_1 = &format!(".L{:?}", self.label_counter);
                        let label_2 = &format!(".L{:?}", self.label_counter + 1);
                        self.label_counter += 2;
                        // skip to label 1 if any value is 0
                        result.push_str(&Self::format_instruction("cmp", vec!["w1", "0"]));
                        result.push_str(&Self::format_instruction("beq", vec![label_1]));
                        result.push_str(&Self::format_instruction("cmp", vec!["w0", "0"]));
                        result.push_str(&Self::format_instruction("beq", vec![label_1]));
                        // otherwise, set result to 1 and skip to end
                        result.push_str(&Self::format_instruction("mov", vec!["w0", "1"]));
                        result.push_str(&Self::format_instruction("b", vec![label_2]));
                        // jump here to set result to 0
                        result.push_str(&format!("{}:\n", label_1));
                        result.push_str(&Self::format_instruction("mov", vec!["w0", "0"]));
                        // mark end of this block
                        result.push_str(&format!("{}:\n", label_2));
                    }
                    Operator::OR => {
                        let label_1 = &format!(".L{:?}", self.label_counter);
                        let label_2 = &format!(".L{:?}", self.label_counter + 1);
                        self.label_counter += 2;
                        // skip to label 1 if any value is not 0
                        result.push_str(&Self::format_instruction("cmp", vec!["w1", "0"]));
                        result.push_str(&Self::format_instruction("bne", vec![label_1]));
                        result.push_str(&Self::format_instruction("cmp", vec!["w0", "0"]));
                        result.push_str(&Self::format_instruction("bne", vec![label_1]));
                        // otherwise, set result to 0 and skip to end
                        result.push_str(&Self::format_instruction("mov", vec!["w0", "0"]));
                        result.push_str(&Self::format_instruction("b", vec![label_2]));
                        // jump here to set result to 1
                        result.push_str(&format!("{}:\n", label_1));
                        result.push_str(&Self::format_instruction("mov", vec!["w0", "1"]));
                        // mark end of this block
                        result.push_str(&format!("{}:\n", label_2));
                    }
                    Operator::Equal => {
                        result.push_str(&Self::format_instruction("cmp", vec!["w1", "w0"]));
                        result.push_str(&Self::format_instruction("cset", vec!["w0", "eq"]));
                    }
                    Operator::NotEqual => {
                        result.push_str(&Self::format_instruction("cmp", vec!["w1", "w0"]));
                        result.push_str(&Self::format_instruction("cset", vec!["w0", "ne"]));
                    }
                    Operator::LessThan => {
                        result.push_str(&Self::format_instruction("cmp", vec!["w1", "w0"]));
                        result.push_str(&Self::format_instruction("cset", vec!["w0", "lt"]));
                    }
                    Operator::LessThanOrEqual => {
                        result.push_str(&Self::format_instruction("cmp", vec!["w1", "w0"]));
                        result.push_str(&Self::format_instruction("cset", vec!["w0", "le"]));
                    }
                    Operator::GreaterThan => {
                        result.push_str(&Self::format_instruction("cmp", vec!["w1", "w0"]));
                        result.push_str(&Self::format_instruction("cset", vec!["w0", "gt"]));
                    }
                    Operator::GreaterThanOrEqual => {
                        result.push_str(&Self::format_instruction("cmp", vec!["w1", "w0"]));
                        result.push_str(&Self::format_instruction("cset", vec!["w0", "ge"]));
                    }
                    _ => {
                        return Err(anyhow!("Not a binary operator"));
                    }
                }
            }
            AstNode::Assign {
                variable,
                expression,
            } => {
                if !self.variable_map.contains_key(variable) {
                    return Err(anyhow!("Variable not declared before assignment"));
                }
                // generate expression
                result.push_str(&self.generate_expression(expression)?);

                // move w0 to location at stack offset
                let stack_offset = self.variable_map.get(variable).unwrap();
                result.push_str(&self.generate_variable_assignment(*stack_offset));
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
        let statement = AstNode::Return { expression };
        let function = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            statement_list: Some(vec![statement]),
        };
        let program = AstNode::Program {
            function_list: vec![function],
        };

        let mut codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        assert_str_trim_eq!(
            result,
            "
                .globl _main
                _main:
                    stp	x29, x30, [sp, -16]!
                    mov	x29, sp
                    mov	w0, #2
                    ldp	x29, x30, [sp], 16
                    ret
            "
        )
    }

    #[test]
    fn test_no_explicit_return() {
        let function = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            statement_list: Some(vec![]),
        };
        let program = AstNode::Program {
            function_list: vec![function],
        };

        let mut codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        assert_str_trim_eq!(
            result,
            "
                .globl _main
                _main:
                    stp	x29, x30, [sp, -16]!
                    mov	x29, sp
                    mov	w0, 0
                    ldp	x29, x30, [sp], 16
                    ret
            "
        )
    }

    #[test]
    fn test_function_declaration() {
        let function = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            statement_list: None,
        };
        let program = AstNode::Program {
            function_list: vec![function],
        };

        let mut codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        // function declaration does not result in generated assembly
        assert_str_trim_eq!(result, "")
    }

    #[test]
    fn test_unary_op() {
        let constant = Box::new(AstNode::Constant { constant: 2 });
        let expression = Box::new(AstNode::UnaryOp {
            operator: Operator::BitwiseComplement,
            factor: constant,
        });
        let statement = AstNode::Return { expression };
        let function = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            statement_list: Some(vec![statement]),
        };
        let program = AstNode::Program {
            function_list: vec![function],
        };

        let mut codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        assert_str_trim_eq!(
            result,
            "
                .globl _main
                _main:
                    stp	x29, x30, [sp, -16]!
                    mov	x29, sp
                    mov	w0, #2
                    mvn	w0, w0
                    ldp	x29, x30, [sp], 16
                    ret
            "
        )
    }

    #[test]
    fn test_stack_push_pop() {
        let mut codegen: Codegen = Codegen::new();
        let mut result = String::new();

        result.push_str(&codegen.generate_push_instruction("w0"));
        assert_eq!(codegen.stack_offset_bytes, -4);
        result.push_str(&codegen.generate_push_instruction("w1"));
        assert_eq!(codegen.stack_offset_bytes, -8);
        result.push_str(&codegen.generate_push_instruction("w2"));
        assert_eq!(codegen.stack_offset_bytes, -12);
        result.push_str(&codegen.generate_push_instruction("w3"));
        assert_eq!(codegen.stack_offset_bytes, -16);
        result.push_str(&codegen.generate_push_instruction("w4"));
        assert_eq!(codegen.stack_offset_bytes, -20);

        result.push_str(&&codegen.generate_pop_instruction("w0"));
        result.push_str(&&codegen.generate_pop_instruction("w1"));
        result.push_str(&&codegen.generate_pop_instruction("w2"));
        result.push_str(&&codegen.generate_pop_instruction("w3"));
        result.push_str(&&codegen.generate_pop_instruction("w4"));
        assert_eq!(codegen.stack_offset_bytes, 0);

        assert_str_trim_eq!(
            result,
            "
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
        let expression = Box::new(AstNode::BinaryOp {
            operator: Operator::Addition,
            expression: constant_1,
            next_expression: constant_2,
        });
        let statement = AstNode::Return { expression };
        let function = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            statement_list: Some(vec![statement]),
        };
        let program = AstNode::Program {
            function_list: vec![function],
        };

        let mut codegen: Codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        assert_str_trim_eq!(
            result,
            "
                .globl _main
                _main:
                    stp	x29, x30, [sp, -16]!
                    mov	x29, sp
                    mov	w0, #1
                    sub	sp, sp, #16
                    str	w0, [sp, 12]
                    mov	w0, #2
                    ldr	w1, [sp, 12]
                    add	sp, sp, 16
                    add	w0, w1, w0
                    ldp	x29, x30, [sp], 16
                    ret
            "
        )
    }

    #[test]
    fn test_and_op() {
        let constant_1 = Box::new(AstNode::Constant { constant: 1 });
        let constant_2 = Box::new(AstNode::Constant { constant: 2 });
        let expression = Box::new(AstNode::BinaryOp {
            operator: Operator::AND,
            expression: constant_1,
            next_expression: constant_2,
        });
        let statement = AstNode::Return { expression };
        let function = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            statement_list: Some(vec![statement]),
        };
        let program = AstNode::Program {
            function_list: vec![function],
        };

        let mut codegen: Codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        assert_str_trim_eq!(
            result,
            "
                .globl _main
                _main:
                    stp	x29, x30, [sp, -16]!
                    mov	x29, sp
                    mov	w0, #1
                    sub	sp, sp, #16
                    str	w0, [sp, 12]
                    mov	w0, #2
                    ldr	w1, [sp, 12]
                    add	sp, sp, 16
                    cmp	w1, 0
                    beq	.L1
                    cmp	w0, 0
                    beq	.L1
                    mov	w0, 1
                    b	.L2
                .L1:
                    mov	w0, 0
                .L2:
                    ldp	x29, x30, [sp], 16
                    ret
            "
        )
    }

    #[test]
    fn test_variable_declaration() {
        let constant_1 = Box::new(AstNode::Constant { constant: 1 });
        let statement_1 = AstNode::Declare {
            variable: "a".into(),
            expression: Some(constant_1),
        };
        let function = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            statement_list: Some(vec![statement_1]),
        };
        let program = AstNode::Program {
            function_list: vec![function],
        };

        let mut codegen: Codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        assert_str_trim_eq!(
            result,
            "
                .globl _main
                _main:
                    stp	x29, x30, [sp, -16]!
                    mov	x29, sp
                    mov	w0, #1
                    sub	sp, sp, #16
                    str	w0, [sp, 12]
                    mov	w0, 0
                    add	sp, sp, 16
                    ldp	x29, x30, [sp], 16
                    ret
            "
        )
    }

    #[test]
    fn test_duplicate_variable_declaration() {
        let constant_1 = Box::new(AstNode::Constant { constant: 1 });
        let constant_2 = Box::new(AstNode::Constant { constant: 2 });
        let statement_1 = AstNode::Declare {
            variable: "a".into(),
            expression: Some(constant_1),
        };
        let statement_2 = AstNode::Declare {
            variable: "a".into(),
            expression: Some(constant_2),
        };
        let function = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            statement_list: Some(vec![statement_1, statement_2]),
        };
        let program = AstNode::Program {
            function_list: vec![function],
        };

        let mut codegen: Codegen = Codegen::new();
        let result = codegen.codegen(program);
        assert!(result.is_err_and(|e| e.to_string() == "Variable already declared"));
    }

    #[test]
    fn test_variable_assignment() {
        let statement_1 = AstNode::Declare {
            variable: "a".into(),
            expression: Some(Box::new(AstNode::Constant { constant: 1 })),
        };
        let statement_2 = AstNode::Declare {
            variable: "b".into(),
            expression: Some(Box::new(AstNode::Constant { constant: 1 })),
        };
        let statement_3 = AstNode::Declare {
            variable: "c".into(),
            expression: Some(Box::new(AstNode::Constant { constant: 1 })),
        };
        let statement_4 = AstNode::Declare {
            variable: "d".into(),
            expression: Some(Box::new(AstNode::Constant { constant: 1 })),
        };
        let statement_5 = AstNode::Declare {
            variable: "e".into(),
            expression: Some(Box::new(AstNode::Constant { constant: 1 })),
        };
        let assignment_1 = AstNode::Assign {
            variable: "a".into(),
            expression: Box::new(AstNode::Constant { constant: 2 }),
        };
        let assignment_2 = AstNode::Assign {
            variable: "b".into(),
            expression: Box::new(AstNode::Constant { constant: 2 }),
        };
        let assignment_3 = AstNode::Assign {
            variable: "c".into(),
            expression: Box::new(AstNode::Constant { constant: 2 }),
        };
        let assignment_4 = AstNode::Assign {
            variable: "d".into(),
            expression: Box::new(AstNode::Constant { constant: 2 }),
        };
        let assignment_5 = AstNode::Assign {
            variable: "e".into(),
            expression: Box::new(AstNode::Constant { constant: 2 }),
        };

        let function = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            statement_list: Some(vec![
                statement_1,
                statement_2,
                statement_3,
                statement_4,
                statement_5,
                assignment_1,
                assignment_2,
                assignment_3,
                assignment_4,
                assignment_5,
            ]),
        };
        let program = AstNode::Program {
            function_list: vec![function],
        };

        let mut codegen: Codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        assert_str_trim_eq!(
            result,
            "
                .globl _main
                _main:
                    stp	x29, x30, [sp, -16]!
                    mov	x29, sp
                    mov	w0, #1
                    sub	sp, sp, #16
                    str	w0, [sp, 12]
                    mov	w0, #1
                    str	w0, [sp, 8]
                    mov	w0, #1
                    str	w0, [sp, 4]
                    mov	w0, #1
                    str	w0, [sp, 0]
                    mov	w0, #1
                    sub	sp, sp, #16
                    str	w0, [sp, 12]
                    mov	w0, #2
                    str	w0, [sp, 28]
                    mov	w0, #2
                    str	w0, [sp, 24]
                    mov	w0, #2
                    str	w0, [sp, 20]
                    mov	w0, #2
                    str	w0, [sp, 16]
                    mov	w0, #2
                    str	w0, [sp, 12]
                    mov	w0, 0
                    add	sp, sp, 32
                    ldp	x29, x30, [sp], 16
                    ret
            "
        )
    }

    #[test]
    fn test_variable_read() {
        let statement_1 = AstNode::Declare {
            variable: "a".into(),
            expression: Some(Box::new(AstNode::Constant { constant: 1 })),
        };
        let statement_2 = AstNode::Declare {
            variable: "b".into(),
            expression: Some(Box::new(AstNode::Constant { constant: 1 })),
        };
        let statement_3 = AstNode::Declare {
            variable: "c".into(),
            expression: Some(Box::new(AstNode::Constant { constant: 1 })),
        };
        let statement_4 = AstNode::Declare {
            variable: "d".into(),
            expression: Some(Box::new(AstNode::Constant { constant: 1 })),
        };
        let statement_5 = AstNode::Declare {
            variable: "e".into(),
            expression: Some(Box::new(AstNode::Constant { constant: 1 })),
        };
        let var_read_1 = AstNode::Variable {
            variable: "a".into(),
        };
        let var_read_2 = AstNode::Variable {
            variable: "b".into(),
        };
        let var_read_3 = AstNode::Variable {
            variable: "c".into(),
        };
        let var_read_4 = AstNode::Variable {
            variable: "d".into(),
        };
        let var_read_5 = AstNode::Variable {
            variable: "e".into(),
        };

        let function = AstNode::Function {
            function_name: "main".into(),
            parameters: vec![],
            statement_list: Some(vec![
                statement_1,
                statement_2,
                statement_3,
                statement_4,
                statement_5,
                var_read_1,
                var_read_2,
                var_read_3,
                var_read_4,
                var_read_5,
            ]),
        };
        let program = AstNode::Program {
            function_list: vec![function],
        };

        let mut codegen: Codegen = Codegen::new();
        let result = codegen.codegen(program).unwrap();
        assert_str_trim_eq!(
            result,
            "
                .globl _main
                _main:
                    stp	x29, x30, [sp, -16]!
                    mov	x29, sp
                    mov	w0, #1
                    sub	sp, sp, #16
                    str	w0, [sp, 12]
                    mov	w0, #1
                    str	w0, [sp, 8]
                    mov	w0, #1
                    str	w0, [sp, 4]
                    mov	w0, #1
                    str	w0, [sp, 0]
                    mov	w0, #1
                    sub	sp, sp, #16
                    str	w0, [sp, 12]
                    ldr	w0, [sp, 28]
                    ldr	w0, [sp, 24]
                    ldr	w0, [sp, 20]
                    ldr	w0, [sp, 16]
                    ldr	w0, [sp, 12]
                    mov	w0, 0
                    add	sp, sp, 32
                    ldp	x29, x30, [sp], 16
                    ret
            "
        )
    }
}
