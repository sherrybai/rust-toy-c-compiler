use itertools::Itertools;
use regex::Regex;
use strum::IntoEnumIterator;
use strum_macros::EnumIter;

use anyhow::anyhow;

#[allow(dead_code)]
#[derive(Clone, Debug, EnumIter, PartialEq)]
pub enum TokenType {
    OpenBrace,
    ClosedBrace,
    OpenParens,
    ClosedParens,
    Semicolon,
    Keyword(String),
    Identifier(String),
    IntLiteral(u32),
    Addition,
    Multiplication,
    Division,
    AND,
    OR,
    // == has to be before = for regex to match
    Equal,
    // != has to be before ! for regex to match
    NotEqual,
    LessThanOrEqual,
    LessThan,
    // >= has to be before > for regex to match
    GreaterThanOrEqual,
    GreaterThan,
    Minus,
    BitwiseComplement,
    LogicalNegation,
    Assignment,
    // TODO: add tokens from stages 6-8
    Comma,
}

impl TokenType {
    pub fn lex(contents: &str) -> anyhow::Result<Vec<Self>> {
        let mut vec: Vec<Self> = vec![];
    
        let re = Regex::new(&Self::get_regex_pattern()[..])?;
        for capture in re.captures_iter(contents) {
            for (i, group) in capture.iter().enumerate() {
                if i == 0 {  // first index indicates overall match
                    continue
                }
                // subsequent index with non-null value indicates the specific capture group that captured the match
                match group {
                    Some(m) => {
                        vec.push(Self::from_index(i, m.as_str())?);
                    },
                    None => ()
                }
            }
        }
        Ok(vec)
    }

    pub fn from_index(i: usize, m: &str) -> anyhow::Result<Self> {
        let Some(variant) = Self::iter().nth(i-1) else {
            return Err(anyhow!("No enum variant found for index {:?}", i));
        };
        match variant {
            Self::Keyword(_) => Ok(Self::Keyword(m.to_string())),
            Self::Identifier(_) => Ok(Self::Identifier(m.to_string())),
            Self::IntLiteral(_) => Ok(Self::IntLiteral(str::parse::<u32>(m)?)),
            _ => Ok(variant)
        }
    }

    pub fn to_regex_pattern(&self) -> &str {
        match self {
            Self::OpenBrace => r"\{",
            Self::ClosedBrace => r"\}",
            Self::OpenParens => r"\(",
            Self::ClosedParens => r"\)",
            Self::Semicolon => r";",
            Self::Keyword(_) => r"int|return",
            Self::Identifier(_) => r"[a-zA-Z]\w*",
            Self::IntLiteral(_) => r"[0-9]+",
            Self::Minus => r"\-",
            Self::BitwiseComplement => r"\~",
            Self::LogicalNegation => r"!",
            Self::Addition => r"\+",
            Self::Multiplication => r"\*",
            Self::Division => r"\/",
            Self::AND => r"&&",
            Self::OR => r"\|\|",
            Self::Equal => r"==",
            Self::NotEqual => r"\!=",
            Self::LessThan => r"<",
            Self::LessThanOrEqual => r"<=",
            Self::GreaterThan => r">",
            Self::GreaterThanOrEqual => r">=",
            Self::Assignment => r"=",
            Self::Comma => r",",
        }
    }

    pub fn get_regex_pattern() -> String {
        Self::iter().map(|t| format!(r"({})", t.to_regex_pattern())).join("|")
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex() {
        let contents = "
            int main() {
                return 2;
            }
        ";
        let expected = vec![
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
        assert_eq!(TokenType::lex(contents).unwrap(), expected);
    }

    #[test]
    fn test_lex_stage_2_unary_ops() {
        let contents = "
            -
            ~
            !
        ";
        let expected = vec![
            TokenType::Minus,
            TokenType::BitwiseComplement,
            TokenType::LogicalNegation,
        ];
        assert_eq!(TokenType::lex(contents).unwrap(), expected);
    }

    #[test]
    fn test_lex_stage_3_binary_ops() {
        let contents = "
            +
            *
            /
        ";
        let expected = vec![
            TokenType::Addition,
            TokenType::Multiplication,
            TokenType::Division,
        ];
        assert_eq!(TokenType::lex(contents).unwrap(), expected);
    }

    #[test]
    fn test_lex_stage_4_binary_ops() {
        let contents = "
            &&
            ||
            ==
            !=
            <
            <=
            >
            >=
        ";
        let expected = vec![
            TokenType::AND,
            TokenType::OR,
            TokenType::Equal,
            TokenType::NotEqual,
            TokenType::LessThan,
            TokenType::LessThanOrEqual,
            TokenType::GreaterThan,
            TokenType::GreaterThanOrEqual
        ];
        assert_eq!(TokenType::lex(contents).unwrap(), expected);
    }

    #[test]
    fn test_lex_stage_5_assignment() {
        let contents = "
            =
        ";
        let expected = vec![
            TokenType::Assignment
        ];
        assert_eq!(TokenType::lex(contents).unwrap(), expected);
    }
}