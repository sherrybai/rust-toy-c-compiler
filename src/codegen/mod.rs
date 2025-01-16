use anyhow::anyhow;
#[cfg(test)]
use assert_str::assert_str_trim_eq;

use crate::parser::AstNode;

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

    let AstNode::Expression{constant} = *expression else {
        return Err(anyhow!("Malformed expression"))
    };
    result.push_str(&format!("{}mov{}w0, #{}\n", INDENT, INDENT, constant));
    result.push_str(&format!("{}ret\n", INDENT));

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_codegen() {
        let expression = Box::new(AstNode::Expression { constant: 2 });
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
}