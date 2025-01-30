# Rust Toy C Compiler

Compiler for a tiny subset of C to AArch64 assembly, written in Rust. Roughly follows Nora Sandler's [Writing a C Compiler series](https://norasandler.com/2017/11/29/Write-a-Compiler.html).

Done as part of my [Recurse Center](https://www.recurse.com/scout/click?t=927165f95f8df92d92538474364eacd7) W2'25 batch.

## Installation
Run `cargo build --release` to build.

## Usage
```
./target/release/rust-toy-c-compiler /path/to/source.c
```
to build assembly `source.s` file in the current directory. Use `gcc` or some other assembler to build the executable:
```
gcc source.s -o source
```
