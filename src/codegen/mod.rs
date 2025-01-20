use anyhow::anyhow;
#[cfg(test)]
use assert_str::assert_str_trim_eq;

use crate::parser::{AstNode, Operator};

const INDENT: &str = "	";

pub fn codegen(ast: AstNode) -> anyhow::Result<String> {
    let AstNode::Program{function} = ast else {
        return Err(anyhow!("Called codegen on node that is not a program"))
    };

    let mut result = String::new();

    // traverse the AST
    let generated_func = generate_function(*function)?;
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
fn generate_function(node: AstNode) -> anyhow::Result<String> {
    let AstNode::Function{identifier, statement} = node else {
        return Err(anyhow!("Called generate_function on node that is not a function"))
    };

    let mut result: String = String::new();

    result.push_str(&format!("{}.globl _{}\n", INDENT, identifier));
    result.push_str(&format!("_{}:\n", identifier));

    // generate statement
    let generated_statement = generate_statement(*statement)?;
    result.push_str(&generated_statement);

    Ok(result)
}

fn generate_statement(node: AstNode) -> anyhow::Result<String> {
    let AstNode::Statement{expression} = node else {
        return Err(anyhow!("Called generate_statement on node that is not a statement"))
    };

    // only return statements supported for now
    let mut result: String = String::new();

    let generated_expression: String = generate_expression(*expression)?;
    result.push_str(&generated_expression);
    result.push_str(&format_instruction("ret", vec![]));

    Ok(result)
}

fn generate_expression(node: AstNode) -> anyhow::Result<String> {
    let mut result: String = String::new();

    match node {
        AstNode::Constant { constant } => {
            let constant_str = format!("#{}", constant);
            result.push_str(&format_instruction("mov", vec!["w0", &constant_str[..]]));
        },
        AstNode::UnaryOp { operator, expression } => {
            let nested_expression = generate_expression(*expression)?;
            result.push_str(&nested_expression);
            // assume previous operation moves the value to w0
            match operator {
                Operator::Negation => {
                    result.push_str(&format_instruction("neg", vec!["w0", "w0"]));
                },
                Operator::BitwiseComplement => {
                    result.push_str(&format_instruction("mvn", vec!["w0", "w0"]));  // logical nor with itself
                },
                Operator::LogicalNegation => {
                    result.push_str(&format_instruction("cmp", vec!["w0", "#0"]));  // compare w0 to 0, setting flag
                    result.push_str(&format_instruction("mov", vec!["w0", "#1"]));  // set w0 to 1 (doesn't clear flags)
                    result.push_str(&format_instruction("csel", vec!["w0", "w0", "wzr", "EQ"]));  // select 1 if true else 0
                }
            }
        }
        _ => {
            return Err(anyhow!("Malformed expression"))
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_codegen() {
        let expression = Box::new(AstNode::Constant { constant: 2 });
        let statement = Box::new(AstNode::Statement {expression});
        let function = Box::new(AstNode::Function {identifier: "main".into(), statement});
        let program = AstNode::Program{function};

        let result = codegen(program).unwrap();
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
        let expression = Box::new(AstNode::UnaryOp { operator: Operator::BitwiseComplement, expression: constant });
        let statement = Box::new(AstNode::Statement {expression});
        let function = Box::new(AstNode::Function {identifier: "main".into(), statement});
        let program = AstNode::Program{function};

        let result = codegen(program).unwrap();
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
}