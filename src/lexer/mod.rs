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
    And,
    Or,
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
    Colon,
    QuestionMark,
    Comma,
}

impl TokenType {
    pub fn lex(contents: &str) -> anyhow::Result<Vec<Self>> {
        let mut vec: Vec<Self> = vec![];

        let re = Regex::new(&Self::get_regex_pattern()[..])?;
        for capture in re.captures_iter(contents) {
            for (i, group) in capture.iter().enumerate() {
                if i == 0 {
                    // first index indicates overall match
                    continue;
                }
                // subsequent index with non-null value indicates the specific capture group that captured the match
                if let Some(m) = group {
                    vec.push(Self::from_index(i, m.as_str())?);
                }
            }
        }
        Ok(vec)
    }

    pub fn from_index(i: usize, m: &str) -> anyhow::Result<Self> {
        let Some(variant) = Self::iter().nth(i - 1) else {
            return Err(anyhow!("No enum variant found for index {:?}", i));
        };
        match variant {
            Self::Keyword(_) => Ok(Self::Keyword(m.to_string())),
            Self::Identifier(_) => Ok(Self::Identifier(m.to_string())),
            Self::IntLiteral(_) => Ok(Self::IntLiteral(str::parse::<u32>(m)?)),
            _ => Ok(variant),
        }
    }

    pub fn to_regex_pattern(&self) -> &str {
        // regex substrings here should not contain nested capture groups '(...)'
        // otherwise `from_index` method will break
        match self {
            Self::OpenBrace => r"\{",
            Self::ClosedBrace => r"\}",
            Self::OpenParens => r"\(",
            Self::ClosedParens => r"\)",
            Self::Semicolon => r";",
            // int, return, if, else, for, while, do, break, continue
            // wrapped by \b to indicate word boundaries
            Self::Keyword(_) => r"\bint\b|\breturn\b|\bif\b|\belse\b|\bfor\b|\bwhile\b|\bdo\b|\bbreak\b|\bcontinue\b",
            Self::Identifier(_) => r"[a-zA-Z]\w*",
            Self::IntLiteral(_) => r"[0-9]+",
            Self::Minus => r"\-",
            Self::BitwiseComplement => r"\~",
            Self::LogicalNegation => r"!",
            Self::Addition => r"\+",
            Self::Multiplication => r"\*",
            Self::Division => r"\/",
            Self::And => r"&&",
            Self::Or => r"\|\|",
            Self::Equal => r"==",
            Self::NotEqual => r"\!=",
            Self::LessThan => r"<",
            Self::LessThanOrEqual => r"<=",
            Self::GreaterThan => r">",
            Self::GreaterThanOrEqual => r">=",
            Self::Assignment => r"=",
            Self::Colon => r":",
            Self::QuestionMark => r"\?",
            Self::Comma => r",",
        }
    }

    pub fn get_regex_pattern() -> String {
        Self::iter()
            .map(|t| format!(r"({})", t.to_regex_pattern()))
            .join("|")
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
            TokenType::And,
            TokenType::Or,
            TokenType::Equal,
            TokenType::NotEqual,
            TokenType::LessThan,
            TokenType::LessThanOrEqual,
            TokenType::GreaterThan,
            TokenType::GreaterThanOrEqual,
        ];
        assert_eq!(TokenType::lex(contents).unwrap(), expected);
    }

    #[test]
    fn test_lex_stage_5_assignment() {
        let contents = "
            =
        ";
        let expected = vec![TokenType::Assignment];
        assert_eq!(TokenType::lex(contents).unwrap(), expected);
    }

    #[test]
    fn test_lex_stage_6_conditionals() {
        let contents = "
            if
            else
            :
            ?
            iff
            tiff
        ";
        let expected = vec![
            TokenType::Keyword("if".into()), 
            TokenType::Keyword("else".into()), 
            TokenType::Colon, 
            TokenType::QuestionMark,
            TokenType::Identifier("iff".into()),
            TokenType::Identifier("tiff".into()),
        ];
        assert_eq!(TokenType::lex(contents).unwrap(), expected);
    }

    #[test]
    fn test_lex_stage_7_loop_keywords() {
        let contents = "
            for
            while
            do
            break
            continue
            doobadeedoo
        ";
        let expected = vec![
            TokenType::Keyword("for".into()), 
            TokenType::Keyword("while".into()), 
            TokenType::Keyword("do".into()), 
            TokenType::Keyword("break".into()), 
            TokenType::Keyword("continue".into()), 
            TokenType::Identifier("doobadeedoo".into()),
        ];
        assert_eq!(TokenType::lex(contents).unwrap(), expected);
    }
}
