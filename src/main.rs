mod codegen;
mod lexer;
mod parser;
mod validation;

use std::fs;
use std::path::Path;

use anyhow::anyhow;
use clap::Parser;
use validation::Validation;

use crate::codegen::Codegen;
use crate::lexer::TokenType;
use crate::parser::AstNode;

#[derive(Parser, Debug)]
#[command(name = "rust-toy-c-compiler")]
#[command(version, about, long_about = None)]
struct Cli {
    filename: String,
}

fn read_file(filename: &str) -> anyhow::Result<String> {
    // Read the contents of the file into a string.
    let contents = fs::read_to_string(filename).expect("Unable to read file");
    Ok(contents)
}

fn get_output_filename(input_filename: &str) -> anyhow::Result<String> {
    let path = Path::new(input_filename);
    let Some(file_stem) = path.file_stem() else {
        return Err(anyhow!("Cannot get file stem from path"));
    };
    let Some(stem_str) = file_stem.to_str() else {
        return Err(anyhow!("Cannot get string from file stem"));
    };
    Ok(format!("{}.s", stem_str))
}

fn main() -> anyhow::Result<()> {
    let args = Cli::parse();
    let contents = match read_file(&args.filename[..]) {
        Ok(contents) => contents,
        Err(e) => return Err(e),
    };
    let lexed: Vec<TokenType> = TokenType::lex(&contents[..])?;
    let parsed: AstNode = AstNode::parse(&lexed[..])?;

    let mut validation = Validation::new();
    validation.validate_ast(&parsed)?;

    let mut codegen = Codegen::new();
    let generated: String = codegen.codegen(parsed)?;

    let output_filename = get_output_filename(&args.filename[..])?;
    fs::write(output_filename, generated).expect("Unable to write file");

    Ok(())
}
