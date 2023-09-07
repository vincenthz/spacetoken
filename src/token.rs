pub use logos::Lexer;
use logos::Logos;
use std::fmt;

/// Integral Number of any precision in base
///
/// To convert to an `u64` (with error handling):
///
/// ```
/// use spacetoken::Number;
///
/// let num = Number::from_str("0x123_456").unwrap();
/// let u = u64::from_str_radix(&num.digits(), num.encoding_radix()).unwrap();
/// assert_eq!(u, 0x123_456);
/// ```
///
/// Or to convert to an arbitrary precision big integer from the `num-bigint` crate:
///
/// ```skip
/// num_bigint::BigInt::parse_bytes(self.digits().as_bytes(), self.encoding_radix()).unwrap()
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Number {
    pub(crate) encoding: NumberEncoding,
    pub(crate) raw: String,
}

/// Number Encoding - enumeration of base 2 (Binary) / 10 (Decimal) / 16 (Hexadecimal)
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum NumberEncoding {
    /// Hexadecimal base-16
    Hexadecimal,
    /// Decimal base-10
    Decimal,
    /// Binary base-2
    Binary,
}

impl NumberEncoding {
    /// Return the radix (base) associated with this encoding
    pub fn radix(self) -> u32 {
        match self {
            Self::Binary => 2,
            Self::Hexadecimal => 16,
            Self::Decimal => 10,
        }
    }
}

/// Group delimiter, one of: () [] {}
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum GroupDelim {
    /// Parenthesis Delimiter ( )
    Parenthesis,
    /// Brace Delimiter { }
    Brace,
    /// Bracket Delimiter [ ]
    Bracket,
}

impl GroupDelim {
    /// Get the character equivalent of this delimiter in start position
    pub fn start_char(self) -> char {
        match self {
            GroupDelim::Parenthesis => '(',
            GroupDelim::Brace => '{',
            GroupDelim::Bracket => '[',
        }
    }

    /// Get the character equivalent of this delimiter in end position
    pub fn end_char(self) -> char {
        match self {
            GroupDelim::Parenthesis => ')',
            GroupDelim::Brace => '}',
            GroupDelim::Bracket => ']',
        }
    }
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.raw)
    }
}

impl Number {
    /// Get the encoding of the number
    pub fn encoding(&self) -> NumberEncoding {
        self.encoding
    }

    /// Get the encoding radix of the number
    pub fn encoding_radix(&self) -> u32 {
        self.encoding.radix()
    }

    /// Get the raw digits as str
    pub fn raw(&self) -> &str {
        &self.raw
    }

    /// Try to parse a number from a raw string
    ///
    /// supported prefix syntax
    /// - 0x or 0X to use hexadecimal base
    /// - 0b or 0B to use binary base
    ///
    /// Content
    pub fn from_str(s: &str) -> Option<Self> {
        if s.is_empty() {
            return None;
        }
        let mut chrs = s.chars();
        let first = chrs.next();
        let second = chrs.next();

        let mut encoding = NumberEncoding::Decimal;
        if let Some(first) = first {
            if let Some(second) = second {
                if first == '0' {
                    if second == 'b' || second == 'B' {
                        encoding = NumberEncoding::Binary;
                    } else if second == 'x' || second == 'X' {
                        encoding = NumberEncoding::Hexadecimal;
                    }
                }
            }
        }

        match encoding {
            NumberEncoding::Decimal => Self::decimal(s),
            NumberEncoding::Hexadecimal => Self::hexadecimal(&chrs.collect::<String>()),
            NumberEncoding::Binary => Self::binary(&chrs.collect::<String>()),
        }
    }

    /// Try to create a decimal number using the str in parameter as the raw digits (0-9 and _)
    pub fn decimal(s: &str) -> Option<Self> {
        if s.chars()
            .find(|c| *c != '_' && !c.is_ascii_digit())
            .is_some()
        {
            println!("X");
            return None;
        }
        Some(Self {
            encoding: NumberEncoding::Decimal,
            raw: s.to_string(),
        })
    }

    /// Try to create a hexadecimal number using the str in parameter as the raw digits (0-9, a-f, A-F and _)
    pub fn hexadecimal(s: &str) -> Option<Self> {
        if s.chars()
            .find(|c| *c != '_' && !c.is_ascii_hexdigit())
            .is_some()
        {
            return None;
        }
        Some(Self {
            encoding: NumberEncoding::Hexadecimal,
            raw: s.to_string(),
        })
    }

    /// Try to create a binary number using the str in parameter as the raw digits (0-1 and _)
    pub fn binary(s: &str) -> Option<Self> {
        if s.chars()
            .find(|c| *c != '_' && *c != '0' && *c != '1')
            .is_some()
        {
            return None;
        }
        Some(Self {
            encoding: NumberEncoding::Binary,
            raw: s.to_string(),
        })
    }

    /// Return only the digits associated with this number without the base
    ///
    /// * 0x7F_03 => 7F03
    /// * 12__345_912 => 12345912
    /// * 0b1111_0000_1010 => 111100001010
    ///
    pub fn digits(&self) -> String {
        self.raw.chars().filter(|v| *v != '_').collect()
    }
}

fn num_bin(lex: &mut Lexer<Token>) -> Option<Number> {
    Number::binary(&lex.slice()[2..])
}

fn num_hex(lex: &mut Lexer<Token>) -> Option<Number> {
    Number::hexadecimal(&lex.slice()[2..])
}

fn num_dec(lex: &mut Lexer<Token>) -> Option<Number> {
    Number::decimal(lex.slice())
}

fn identifier(lex: &mut Lexer<Token>) -> Option<String> {
    Some(lex.slice().to_string())
}

fn operator(lex: &mut Lexer<Token>) -> Option<char> {
    lex.slice().chars().next()
}

fn quoted_string(lex: &mut Lexer<Token>) -> Option<String> {
    let slice = lex.remainder().as_bytes();
    let mut i = 0;
    let mut escape = false;
    loop {
        if slice[i] == b'"' {
            if !escape {
                break;
            }
        }
        if !escape && slice[i] == b'\\' {
            escape = true;
        } else {
            escape = false;
        }

        i += 1
    }
    lex.bump(i + 1);
    Some(std::str::from_utf8(&slice[0..i]).unwrap().to_string())
}

fn group_start(lex: &mut Lexer<Token>) -> Option<GroupDelim> {
    lex.slice().chars().next().and_then(|c| {
        if c == GroupDelim::Parenthesis.start_char() {
            Some(GroupDelim::Parenthesis)
        } else if c == GroupDelim::Brace.start_char() {
            Some(GroupDelim::Brace)
        } else if c == GroupDelim::Bracket.start_char() {
            Some(GroupDelim::Bracket)
        } else {
            None
        }
    })
}

fn group_end(lex: &mut Lexer<Token>) -> Option<GroupDelim> {
    lex.slice().chars().next().and_then(|c| {
        if c == GroupDelim::Parenthesis.end_char() {
            Some(GroupDelim::Parenthesis)
        } else if c == GroupDelim::Brace.end_char() {
            Some(GroupDelim::Brace)
        } else if c == GroupDelim::Bracket.end_char() {
            Some(GroupDelim::Bracket)
        } else {
            None
        }
    })
}

fn comment(lex: &mut Lexer<Token>) -> Option<String> {
    // if we don't find it, then we'll just finish there
    match lex.remainder().find("\n") {
        Some(len) => {
            let comment = lex.remainder()[0..len].to_string();
            lex.bump(len + 1);
            Some(comment)
        }
        None => {
            let comment = lex.remainder().to_string();
            lex.bump(lex.remainder().len());
            Some(comment)
        }
    }
}

/// Parameters for the Lexer
#[derive(Default, Clone, Debug)]
pub struct Parameters {}

// ` and ' not used
#[derive(Logos, Debug, PartialEq, Eq, Clone)]
#[logos(skip r#"[ \t\n\f]+"#)]
#[logos(subpattern decimal = r"[0-9][_0-9]*")]
#[logos(subpattern hex = r"_*[0-9a-fA-F][_0-9a-fA-F]*")]
#[logos(subpattern binary = r"_*[0-1][_0-1]*")]
#[logos(subpattern ident = r"(\p{XID_Start}|_)\p{XID_Continue}*")]
#[logos(subpattern operator = r"([-!?|#&@~:;+*/%=$^<>.]|\p{Math_Symbol})")]
#[logos(extras = Parameters)]
/// Token generated by the lexer
///
/// ```rust
/// use logos::Logos;
/// use spacetoken::Token;
///
/// let mut lex = Token::lex("my content");
/// let first = lex.next().expect("has first");
/// let second = lex.next().expect("has second");
/// assert!(lex.next().is_none(), "stream is finished");
///
/// assert_eq!(first, Token::Ident("my".to_string()));
/// assert_eq!(second, Token::Ident("content".to_string()));
///
/// ```
pub enum Token {
    /// Start of a group, either (, [ or {
    #[regex("[{\\[\\(]", group_start)]
    GroupStart(GroupDelim),

    /// End of a group, either ), ] or }
    #[regex("[}\\]\\)]", group_end)]
    GroupEnd(GroupDelim),

    /// Punctuation only one character like . , @ ! and the Unicode math symbols
    #[regex("(?&operator)", operator, priority = 2)]
    Punct(char),

    /// Number in either binary, hexadecimal or decimal form
    #[regex("0[bB](?&binary)", num_bin)]
    #[regex("0[xX](?&hex)", num_hex)]
    #[regex("(?&decimal)", num_dec)]
    Number(Number),

    /// Identifier
    #[regex("(?&ident)", identifier)]
    Ident(String),

    /// Quoted String starting and ending with the " character
    #[token("\"", quoted_string)]
    String(String),

    /// Comment
    #[token("//", comment)]
    Comment(String),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::GroupStart(delim) => write!(f, "{}", delim.start_char()),
            Token::GroupEnd(delim) => write!(f, "{}", delim.end_char()),
            Token::Ident(id) => write!(f, "{}", id),
            Token::String(s) => write!(f, "\"{}\"", s),
            Token::Number(number) => write!(f, "{}", number),
            Token::Punct(op) => write!(f, "{}", op),
            Token::Comment(s) => write!(f, "//{}", s),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_lex {
        ($s:literal, $v:expr) => {{
            let mut lex = Token::lexer($s);
            let expected = $v;
            let mut exp_it = expected.into_iter();
            let mut pos = 1;
            loop {
                match (lex.next(), exp_it.next()) {
                    (Some(Err(e)), Some(exp)) => {
                        panic!(
                            "token at position {}\nexpected : {:?}\ngot     : <error> {:?}",
                            pos, exp, e
                        )
                    }
                    (Some(Ok(got)), Some(exp)) => {
                        assert_eq!(
                            &got, exp,
                            "token at position {}\nexpected : {:?}\ngot     : {:?}",
                            pos, exp, got
                        )
                    }
                    (Some(Err(e)), None) => {
                        panic!(
                            "token at position {}\nexpected : <EOF>\ngot     : <error> {:?}",
                            pos, e
                        )
                    }
                    (Some(Ok(got)), None) => {
                        panic!(
                            "token at position {}\nexpected : <EOF>\ngot     : {:?}",
                            pos, got
                        )
                    }
                    (None, Some(exp)) => {
                        panic!(
                            "token at position {}\nexpected : {:?}\ngot     : <EOF>",
                            pos, exp
                        )
                    }
                    (None, None) => {
                        break;
                    }
                }
                pos += 1;
            }
        }};
    }

    fn token_num(encoding: NumberEncoding, s: &str) -> Token {
        Token::Number(Number {
            encoding,
            raw: s.to_string(),
        })
    }

    fn token_dec(s: &str) -> Token {
        token_num(NumberEncoding::Decimal, s)
    }

    fn token_hex(s: &str) -> Token {
        token_num(NumberEncoding::Hexadecimal, s)
    }

    fn token_bin(s: &str) -> Token {
        token_num(NumberEncoding::Binary, s)
    }

    fn token_ident(s: &str) -> Token {
        Token::Ident(s.to_string())
    }

    fn token_punct(c: char) -> Token {
        Token::Punct(c)
    }

    #[test]
    fn numbers() {
        test_lex!("1", &[token_dec("1")]);
        test_lex!("0x7F_12", &[token_hex("7F_12")]);
        test_lex!("0b_00_11_10", &[token_bin("_00_11_10")]);
    }

    #[test]
    fn groups() {
        test_lex!(
            "( )",
            &[
                Token::GroupStart(GroupDelim::Parenthesis),
                Token::GroupEnd(GroupDelim::Parenthesis),
            ]
        );
        test_lex!(
            "( } [ )",
            &[
                Token::GroupStart(GroupDelim::Parenthesis),
                Token::GroupEnd(GroupDelim::Brace),
                Token::GroupStart(GroupDelim::Bracket),
                Token::GroupEnd(GroupDelim::Parenthesis),
            ]
        )
    }

    #[test]
    fn strings() {
        test_lex!(
            r#""this is a string""#,
            &[Token::String("this is a string".to_string()),]
        )
    }

    #[test]
    fn puncts() {
        test_lex!(
            "+!@",
            &[Token::Punct('+'), Token::Punct('!'), Token::Punct('@')]
        );
        test_lex!("⊗", &[Token::Punct('⊗')]);
        test_lex!("⊗+", &[Token::Punct('⊗'), Token::Punct('+')]);
    }

    #[test]
    fn comments() {
        test_lex!(
            r#"// this is a comment
123 [
            "#,
            &[
                Token::Comment(" this is a comment".to_string()),
                token_dec("123"),
                Token::GroupStart(GroupDelim::Bracket),
            ]
        )
    }

    #[test]
    fn complete() {
        test_lex!(
            "let x = 12_3; { function return () + ! @@$ }",
            &[
                token_ident("let"),
                token_ident("x"),
                token_punct('='),
                token_dec("12_3"),
                token_punct(';'),
                Token::GroupStart(GroupDelim::Brace),
                token_ident("function"),
                token_ident("return"),
                Token::GroupStart(GroupDelim::Parenthesis),
                Token::GroupEnd(GroupDelim::Parenthesis),
                token_punct('+'),
                token_punct('!'),
                token_punct('@'),
                token_punct('@'),
                token_punct('$'),
                Token::GroupEnd(GroupDelim::Brace),
            ]
        );
        test_lex!(
            "αφήνω x = 12_3 ⊛ 观点;",
            &[
                token_ident("αφήνω"),
                token_ident("x"),
                token_punct('='),
                token_dec("12_3"),
                token_punct('⊛'),
                token_ident("观点"),
                token_punct(';'),
            ]
        )
    }
}
