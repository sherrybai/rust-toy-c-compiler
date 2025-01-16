mod lexer;
mod parser;

use std::fs::File;
use std::io::Read;

use clap::Parser;

use crate::lexer::lex;
use crate::lexer::TokenType;


#[derive(Parser, Debug)]
#[command(name = "rust-toy-c-compiler")]
#[command(version, about, long_about = None)]
struct Cli {
    filename: String
}

fn read_file(filename: String) -> anyhow::Result<String> {
    // Read the contents of the file into a string.
    let mut file = File::open(filename)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}

fn main() -> anyhow::Result<()> {
    let args = Cli::parse();
    let contents = match read_file(args.filename) {
        Ok(contents)=> contents,
        Err(e) => return Err(e),
    };
    println!("{}", contents);
    let lexed: Vec<TokenType> = lex(&contents[..]);
    println!("{:?}", lexed);
    Ok(())
}
