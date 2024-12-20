use crate::parse::{ParseError, Parser, Token};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Numeral(pub String);
impl std::fmt::Display for Numeral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(rest) = self.0.strip_prefix('-') {
            write!(f, "(- {rest})")
        } else {
            write!(f, "{}", self.0)
        }
    }
}
impl SmtlibParse for Numeral {
    fn is_start_of(offset: usize, tokens: &mut Parser) -> bool {
        tokens.nth(offset) == Token::Numeral
    }

    fn parse(tokens: &mut Parser) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect(Token::Numeral)?.into()))
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Decimal(pub String);
impl std::fmt::Display for Decimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl SmtlibParse for Decimal {
    fn is_start_of(offset: usize, tokens: &mut Parser) -> bool {
        tokens.nth(offset) == Token::Decimal
    }

    fn parse(tokens: &mut Parser) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect(Token::Decimal)?.into()))
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Symbol(pub String);
impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl SmtlibParse for Symbol {
    fn is_start_of(offset: usize, tokens: &mut Parser) -> bool {
        tokens.nth(offset) == Token::Symbol
    }

    fn parse(tokens: &mut Parser) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect(Token::Symbol)?.into()))
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Hexadecimal(pub String);
impl std::fmt::Display for Hexadecimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl SmtlibParse for Hexadecimal {
    fn is_start_of(offset: usize, tokens: &mut Parser) -> bool {
        tokens.nth(offset) == Token::Hexadecimal
    }

    fn parse(tokens: &mut Parser) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect(Token::Hexadecimal)?.into()))
    }
}
impl Hexadecimal {
    pub fn parse(&self) -> Result<i64, std::num::ParseIntError> {
        i64::from_str_radix(&self.0[2..], 16)
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Binary(pub String);
impl std::fmt::Display for Binary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl SmtlibParse for Binary {
    fn is_start_of(offset: usize, tokens: &mut Parser) -> bool {
        tokens.nth(offset) == Token::Binary
    }

    fn parse(tokens: &mut Parser) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect(Token::Binary)?.into()))
    }
}
impl Binary {
    pub fn parse(&self) -> Result<i64, std::num::ParseIntError> {
        i64::from_str_radix(&self.0[2..], 2)
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Reserved(pub String);
impl std::fmt::Display for Reserved {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl SmtlibParse for Reserved {
    fn is_start_of(offset: usize, tokens: &mut Parser) -> bool {
        tokens.nth(offset) == Token::Reserved
    }

    fn parse(tokens: &mut Parser) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect(Token::Reserved)?.into()))
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Keyword(pub String);
impl std::fmt::Display for Keyword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl SmtlibParse for Keyword {
    fn is_start_of(offset: usize, tokens: &mut Parser) -> bool {
        tokens.nth(offset) == Token::Keyword
    }

    fn parse(tokens: &mut Parser) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect(Token::Keyword)?.into()))
    }
}

pub type BValue = bool;

pub(crate) trait SmtlibParse: Sized {
    fn is_start_of(offset: usize, tokens: &mut Parser) -> bool;
    fn parse(tokens: &mut Parser) -> Result<Self, ParseError>;
}

impl SmtlibParse for String {
    fn is_start_of(offset: usize, tokens: &mut Parser) -> bool {
        tokens.nth(offset) == Token::String
    }

    fn parse(tokens: &mut Parser) -> Result<Self, ParseError> {
        Ok(tokens.expect(Token::String)?.into())
    }
}
impl SmtlibParse for bool {
    fn is_start_of(_offset: usize, _tokens: &mut Parser) -> bool {
        todo!()
    }

    fn parse(_tokens: &mut Parser) -> Result<Self, ParseError> {
        todo!()
    }
}
