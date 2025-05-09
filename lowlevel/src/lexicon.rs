use crate::parse::{ParseError, Parser, Token};

/// **Numerals.** A `<numeral>` is the digit `0 or a non-empty sequence of
/// digits not starting with `0`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Numeral<'st> {
    repr: NumeralRepr<'st>,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
enum NumeralRepr<'st> {
    Number(u128),
    String(&'st str),
}
impl std::fmt::Debug for Numeral<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.repr {
            NumeralRepr::Number(n) => f.debug_tuple("Numeral").field(&n).finish(),
            NumeralRepr::String(s) => f.debug_tuple("Numeral").field(&s).finish(),
        }
    }
}
#[derive(Debug, thiserror::Error, Clone)]
pub enum NumeralError {
    #[error("invalid numeral")]
    Invalid,
}
impl Numeral<'_> {
    pub const fn from_u128(n: u128) -> Numeral<'static> {
        Numeral {
            repr: NumeralRepr::Number(n),
        }
    }
    pub const fn from_usize(n: usize) -> Numeral<'static> {
        Numeral {
            repr: NumeralRepr::Number(n as _),
        }
    }
}
impl<'st> Numeral<'st> {
    pub fn try_from_str(s: &'st str) -> Result<Numeral<'st>, NumeralError> {
        if s == "0" {
            Ok(Numeral {
                repr: NumeralRepr::Number(0),
            })
        } else if s.chars().all(|c| c.is_ascii_digit()) {
            Ok(Self::from_validated_str(s))
        } else {
            Err(NumeralError::Invalid)
        }
    }
    fn from_validated_str(s: &'st str) -> Self {
        match s.parse() {
            Ok(n) => Self {
                repr: NumeralRepr::Number(n),
            },
            Err(_) => Self {
                repr: NumeralRepr::String(s),
            },
        }
    }
    pub fn into_u128(self) -> Result<u128, &'st str> {
        match self.repr {
            NumeralRepr::Number(n) => Ok(n),
            NumeralRepr::String(s) => Err(s),
        }
    }
}

impl std::fmt::Display for Numeral<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.repr {
            NumeralRepr::Number(n) => write!(f, "{n}"),
            NumeralRepr::String(s) => write!(f, "{s}"),
        }
    }
}
impl<'st> SmtlibParse<'st> for Numeral<'st> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'st, '_>) -> bool {
        tokens.nth(offset) == Token::Numeral
    }
    fn parse(tokens: &mut Parser<'st, '_>) -> Result<Self, ParseError> {
        let token = tokens.expect_st(Token::Numeral)?;
        Ok(Numeral::from_validated_str(token))
    }
}
impl From<u128> for Numeral<'_> {
    fn from(value: u128) -> Self {
        Numeral::from_u128(value)
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Decimal<'st>(pub &'st str);
impl std::fmt::Display for Decimal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'st> SmtlibParse<'st> for Decimal<'st> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'st, '_>) -> bool {
        tokens.nth(offset) == Token::Decimal
    }
    fn parse(tokens: &mut Parser<'st, '_>) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect_st(Token::Decimal)?))
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Symbol<'st>(pub &'st str);
impl std::fmt::Display for Symbol<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'st> SmtlibParse<'st> for Symbol<'st> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'st, '_>) -> bool {
        tokens.nth(offset) == Token::Symbol
    }
    fn parse(tokens: &mut Parser<'st, '_>) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect_st(Token::Symbol)?))
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Hexadecimal<'st>(pub &'st str);
impl std::fmt::Display for Hexadecimal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'st> SmtlibParse<'st> for Hexadecimal<'st> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'st, '_>) -> bool {
        tokens.nth(offset) == Token::Hexadecimal
    }
    fn parse(tokens: &mut Parser<'st, '_>) -> Result<Self, ParseError> {
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
pub struct Binary<'st>(pub &'st str);
impl std::fmt::Display for Binary<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'st> SmtlibParse<'st> for Binary<'st> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'st, '_>) -> bool {
        tokens.nth(offset) == Token::Binary
    }
    fn parse(tokens: &mut Parser<'st, '_>) -> Result<Self, ParseError> {
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
pub struct Reserved<'st>(pub &'st str);
impl std::fmt::Display for Reserved<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'st> SmtlibParse<'st> for Reserved<'st> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'st, '_>) -> bool {
        tokens.nth(offset) == Token::Reserved
    }
    fn parse(tokens: &mut Parser<'st, '_>) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect_st(Token::Reserved)?))
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Keyword<'st>(pub &'st str);
impl std::fmt::Display for Keyword<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl<'st> SmtlibParse<'st> for Keyword<'st> {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'st, '_>) -> bool {
        tokens.nth(offset) == Token::Keyword
    }
    fn parse(tokens: &mut Parser<'st, '_>) -> Result<Self, ParseError> {
        Ok(Self(tokens.expect_st(Token::Keyword)?))
    }
}

pub type BValue = bool;

pub(crate) trait SmtlibParse<'st>: Sized {
    type Output: Clone;

    fn is_start_of(offset: usize, tokens: &mut Parser<'st, '_>) -> bool;
    fn parse(tokens: &mut Parser<'st, '_>) -> Result<Self::Output, ParseError>;
}

impl<'st> SmtlibParse<'st> for String {
    type Output = &'st str;
    fn is_start_of(offset: usize, tokens: &mut Parser<'st, '_>) -> bool {
        tokens.nth(offset) == Token::String
    }
    fn parse(tokens: &mut Parser<'st, '_>) -> Result<Self::Output, ParseError> {
        tokens.expect_st(Token::String)
    }
}
impl<'st> SmtlibParse<'st> for &'st str {
    type Output = Self;
    fn is_start_of(offset: usize, tokens: &mut Parser<'st, '_>) -> bool {
        tokens.nth(offset) == Token::String
    }

    fn parse(tokens: &mut Parser<'st, '_>) -> Result<Self, ParseError> {
        tokens.expect_st(Token::String)
    }
}
impl<'st> SmtlibParse<'st> for bool {
    type Output = Self;
    fn is_start_of(_offset: usize, _tokens: &mut Parser<'st, '_>) -> bool {
        todo!()
    }

    fn parse(_tokens: &mut Parser<'st, '_>) -> Result<Self, ParseError> {
        todo!()
    }
}
