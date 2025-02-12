use crate::parse::{ParseError, Parser, Token};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Numeral<'src>(pub &'src str);
impl std::fmt::Display for Numeral<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(rest) = self.0.strip_prefix('-') {
            write!(f, "(- {rest})")
        } else {
            write!(f, "{}", self.0)
        }
    }
}
impl<'src> SmtlibParse<'src> for Numeral<'src> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'src, '_>) -> bool {
        tokens.nth(offset) == Token::Numeral
    }
    fn parse(tokens: &mut Parser<'src, '_>) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect_st(Token::Numeral)?))
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Decimal<'src>(pub &'src str);
impl std::fmt::Display for Decimal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'src> SmtlibParse<'src> for Decimal<'src> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'src, '_>) -> bool {
        tokens.nth(offset) == Token::Decimal
    }
    fn parse(tokens: &mut Parser<'src, '_>) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect_st(Token::Decimal)?))
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Symbol<'src>(pub &'src str);
impl std::fmt::Display for Symbol<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'src> SmtlibParse<'src> for Symbol<'src> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'src, '_>) -> bool {
        tokens.nth(offset) == Token::Symbol
    }
    fn parse(tokens: &mut Parser<'src, '_>) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect_st(Token::Symbol)?))
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Hexadecimal<'src>(pub &'src str);
impl std::fmt::Display for Hexadecimal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'src> SmtlibParse<'src> for Hexadecimal<'src> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'src, '_>) -> bool {
        tokens.nth(offset) == Token::Hexadecimal
    }
    fn parse(tokens: &mut Parser<'src, '_>) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect_st(Token::Hexadecimal)?))
    }
}
impl Hexadecimal<'_> {
    pub fn parse(&self) -> Result<i64, std::num::ParseIntError> {
        i64::from_str_radix(&self.0[2..], 16)
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Binary<'src>(pub &'src str);
impl std::fmt::Display for Binary<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'src> SmtlibParse<'src> for Binary<'src> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'src, '_>) -> bool {
        tokens.nth(offset) == Token::Binary
    }
    fn parse(tokens: &mut Parser<'src, '_>) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect_st(Token::Binary)?))
    }
}
impl Binary<'_> {
    pub fn parse(&self) -> Result<i64, std::num::ParseIntError> {
        i64::from_str_radix(&self.0[2..], 2)
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Reserved<'src>(pub &'src str);
impl std::fmt::Display for Reserved<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'src> SmtlibParse<'src> for Reserved<'src> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'src, '_>) -> bool {
        tokens.nth(offset) == Token::Reserved
    }
    fn parse(tokens: &mut Parser<'src, '_>) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect_st(Token::Reserved)?))
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Keyword<'src>(pub &'src str);
impl std::fmt::Display for Keyword<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'src> SmtlibParse<'src> for Keyword<'src> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'src, '_>) -> bool {
        tokens.nth(offset) == Token::Keyword
    }
    fn parse(tokens: &mut Parser<'src, '_>) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect_st(Token::Keyword)?))
    }
}

pub type BValue = bool;

pub(crate) trait SmtlibParse<'src>: Sized {
    type Output: Clone;

    fn is_start_of(offset: usize, tokens: &mut Parser<'src, '_>) -> bool;
    fn parse(tokens: &mut Parser<'src, '_>) -> Result<Self::Output, ParseError>;
}

impl<'src> SmtlibParse<'src> for String {
    type Output = &'src str;
    fn is_start_of(offset: usize, tokens: &mut Parser<'src, '_>) -> bool {
        tokens.nth(offset) == Token::String
    }
    fn parse(tokens: &mut Parser<'src, '_>) -> Result<Self::Output, ParseError> {
        tokens.expect_st(Token::String)
    }
}
impl<'src> SmtlibParse<'src> for &'src str {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'src, '_>) -> bool {
        tokens.nth(offset) == Token::String
    }

    fn parse(tokens: &mut Parser<'src, '_>) -> Result<Self, ParseError> {
        tokens.expect_st(Token::String)
    }
}
impl<'src> SmtlibParse<'src> for bool {
    type Output = Self;
    fn is_start_of(_offset: usize, _tokens: &mut Parser<'src, '_>) -> bool {
        todo!()
    }

    fn parse(_tokens: &mut Parser<'src, '_>) -> Result<Self, ParseError> {
        todo!()
    }
}
