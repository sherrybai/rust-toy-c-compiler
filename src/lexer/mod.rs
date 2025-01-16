use itertools::Itertools;
use regex::Regex;
use strum::IntoEnumIterator;
use strum_macros::EnumIter;

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
    IntLiteral(u64),
}

impl TokenType {
    pub fn from_index(i: usize, m: &str) -> TokenType{
        let variant = TokenType::iter().nth(i-1).unwrap();  // TODO: fix later
        match variant {
            Self::Keyword(_) => Self::Keyword(m.to_string()),
            Self::Identifier(_) => Self::Identifier(m.to_string()),
            Self::IntLiteral(_) => Self::IntLiteral(str::parse::<u64>(m).unwrap()),  // TODO: fix later
            _ => variant
        }
    }

    pub fn to_regex_pattern(&self) -> &str {
        use TokenType::*;

        match self {
            OpenBrace => r"\{",
            ClosedBrace => r"\}",
            OpenParens => r"\(",
            ClosedParens => r"\)",
            Semicolon => r";",
            Keyword(_) => r"int|return",
            Identifier(_) => r"[a-zA-Z]\w*",
            IntLiteral(_) => r"[0-9]+"
        }
    }

    pub fn get_regex_pattern() -> String {
        TokenType::iter().map(|t| format!(r"({})", t.to_regex_pattern())).join("|")
    }
}


pub fn lex(contents: &str) -> Vec<TokenType> {
    let mut vec: Vec<TokenType> = vec![];

    let re = Regex::new(&TokenType::get_regex_pattern()[..]).unwrap();  // Fix this later
    for capture in re.captures_iter(contents) {
        for (i, group) in capture.iter().enumerate() {
            if i == 0 {  // first index indicates overall match
                continue
            }
            // subsequent index with non-null value indicates the specific capture group that captured the match
            match group {
                Some(m) => {
                    vec.push(TokenType::from_index(i, m.as_str()));
                },
                None => ()
            }
        }
    }
    vec
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
        assert_eq!(lex(contents), expected);
    }

}