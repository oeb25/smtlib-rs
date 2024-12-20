use itertools::Itertools;

use crate::lexicon::SmtlibParse;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, logos::Logos)]
pub(crate) enum Token {
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,

    /// A ⟨numeral⟩ is the digit 0 or a non-empty sequence of digits not
    /// starting with 0 .
    #[regex("0|([1-9][0-9]*)", priority = 2)]
    Numeral,

    /// A ⟨decimal⟩ is a token of the form ⟨numeral⟩.0∗⟨numeral⟩ .
    #[regex(r"(0|([1-9][0-9]*))\.[0-9]+", priority = 2)]
    Decimal,

    /// A ⟨hexadecimal⟩ is a non-empty case-insensitive sequence of digits and
    /// letters from A to F preceded by the (case sensitive) characters #x.
    #[regex("#x[0-9a-fA-F]+")]
    Hexadecimal,

    /// A ⟨binary⟩ is a non-empty sequence of the characters 0 and 1 preceded by
    /// the characters #b.
    #[regex("#b[01]+")]
    Binary,

    /// A ⟨string⟩ (literal) is any sequence of characters from ⟨printable_char⟩
    /// or ⟨white_space_char⟩ delimited by the double quote character " (34dec).
    /// The character " can itself occur within a string literal only if
    /// duplicated. In other words, after an initial " that starts a literal, a
    /// lexer should treat the sequence "" as an escape sequence denoting a
    /// single occurrence of " within the literal.
    #[regex(r#"("[^"]*")+"#)]
    String,

    /// The language uses a number of reserved words, sequences of printable
    /// characters that are to be treated as individual tokens. The basic set of
    /// reserved words consists of the following:
    ///
    /// ```ignore
    /// BINARY DECIMAL HEXADECIMAL NUMERAL STRING _ ! as let exists forall match par
    /// ```
    ///
    /// Additionally, each
    /// command name in the scripting language defined in Section 3.9
    /// (`set-logic`, `set-option`, . . . ) is also a reserved word.
    #[token("_", priority = 2)]
    #[token("!", priority = 2)]
    #[token("as")]
    #[token("BINARY")]
    #[token("DECIMAL")]
    #[token("exists")]
    #[token("forall")]
    #[token("HEXADECIMAL")]
    #[token("let")]
    #[token("match")]
    #[token("NUMERAL")]
    #[token("par")]
    #[token("STRING")]
    #[token("assert")]
    #[token("check-sat")]
    #[token("check-sat-assuming")]
    #[token("declare-const")]
    #[token("declare-datatype")]
    #[token("declare-datatypes")]
    #[token("declare-fun")]
    #[token("declare-sort")]
    #[token("define-fun")]
    #[token("define-fun-rec")]
    #[token("define-sort")]
    #[token("echo")]
    #[token("exit")]
    #[token("get-assertions")]
    #[token("get-assignment")]
    #[token("get-info")]
    #[token("get-model")]
    #[token("get-option")]
    #[token("get-proof")]
    #[token("get-unsat-assumptions")]
    #[token("get-unsat-core")]
    #[token("get-value")]
    #[token("pop")]
    #[token("push")]
    #[token("reset")]
    #[token("reset-assertions")]
    #[token("set-info")]
    #[token("set-logic")]
    #[token("set-option")]
    Reserved,

    /// A ⟨symbol⟩ is either a simple symbol or a quoted symbol. A simple symbol
    /// is any non-empty sequence of elements of ⟨letter⟩ and ⟨digit⟩ and the
    /// characters
    ///
    /// ```ignore
    /// ~ ! @ $ % ^ & * _ - + = < > . ? /
    /// ```
    ///
    /// that does not start with a digit and is not a reserved word.
    #[regex(r"[~!@$%^&*_\-+=<>.?/a-zA-Z0-9]+", priority = 1)]
    #[regex(r"\|[^|\\]+\|")]
    Symbol,

    /// A ⟨keyword⟩ is a token of the form `:⟨simple_symbol⟩`. Elements of this
    /// category have a special use in the language. They are used as attribute
    /// names or option names.
    #[regex(r":[~!@$%^&*_\-+=<>.?/a-zA-Z0-9]+")]
    Keyword,

    /// White Space Characters. A ⟨white_space_char⟩ is one of the following
    /// characters: 9dec (tab), 10dec (line feed), 13dec (carriage return), and
    /// 32dec (space).
    #[regex(r"[\t\n\r ]+", logos::skip)]
    #[regex(r";[^\n]*", logos::skip)]
    Error,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceSpan {
    /// The start of the span.
    offset: usize,
    /// The total length of the span. Think of this as an offset from `start`.
    length: usize,
}

impl SourceSpan {
    #[must_use]
    pub fn offset(&self) -> usize {
        self.offset
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.length
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[must_use]
    pub fn join(&self, span: SourceSpan) -> SourceSpan {
        let offset = self.offset.min(span.offset);
        let end = self.end().max(span.end());
        let length = end - offset;
        SourceSpan { offset, length }
    }

    #[must_use]
    pub fn end(&self) -> usize {
        self.offset + self.length
    }

    #[must_use]
    pub fn contains(&self, byte_offset: usize) -> bool {
        self.offset() <= byte_offset && byte_offset < self.end()
    }

    #[must_use]
    pub fn union(
        init: SourceSpan,
        span: impl IntoIterator<Item = Option<SourceSpan>>,
    ) -> SourceSpan {
        span.into_iter()
            .fold(init, |a, b| b.map(|b| a.join(b)).unwrap_or(a))
    }
}

impl From<SourceSpan> for miette::SourceSpan {
    fn from(s: SourceSpan) -> Self {
        Self::new(s.offset.into(), s.length.into())
    }
}
impl From<(usize, usize)> for SourceSpan {
    fn from((offset, length): (usize, usize)) -> Self {
        SourceSpan { offset, length }
    }
}

#[derive(Debug, Clone, Copy, Eq)]
pub(crate) struct Spanned<T>(pub(crate) T, pub(crate) SourceSpan);
impl<S> From<Spanned<S>> for SourceSpan {
    fn from(value: Spanned<S>) -> Self {
        value.1
    }
}
impl<S> From<Spanned<S>> for miette::SourceSpan {
    fn from(value: Spanned<S>) -> Self {
        value.1.into()
    }
}

impl<S: std::fmt::Display> std::fmt::Display for Spanned<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: PartialEq> PartialEq for Spanned<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<T: std::hash::Hash> std::hash::Hash for Spanned<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

#[derive(Debug, thiserror::Error, miette::Diagnostic, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[error("{error}")]
pub struct ParseError {
    error: String,
    #[source_code]
    src: String,
    #[label("{}", label.as_ref().map(|s| s.as_str()).unwrap_or_else(|| "here"))]
    err_span: SourceSpan,
    label: Option<String>,
    #[help]
    help: Option<String>,
}

#[derive(Debug)]
pub(crate) struct Parser<'src> {
    src: &'src str,
    cursor: usize,
    lexer: Vec<(Token, SourceSpan)>,
    errors: Vec<ParseError>,
}

impl<'src> Parser<'src> {
    pub(crate) fn new(src: &'src str) -> Self {
        let lexer = logos::Lexer::<'src, Token>::new(src)
            .spanned()
            .map(|(t, r)| {
                (
                    t.unwrap_or(Token::Error),
                    SourceSpan::from((r.start, r.len())),
                )
            })
            .collect_vec();

        Parser {
            src,
            cursor: 0,
            lexer,
            errors: vec![],
        }
    }

    pub(crate) fn current(&self) -> Token {
        self.nth(0)
    }

    pub(crate) fn nth_span(&self, n: usize) -> SourceSpan {
        self.nth_raw(n).1
    }

    pub(crate) fn current_span(&self) -> SourceSpan {
        self.nth_span(0)
    }

    pub(crate) fn nth_str(&self, n: usize) -> &'src str {
        let span = self.nth_span(n);
        &self.src[span.offset()..span.end()]
    }

    pub(crate) fn current_str(&self) -> &'src str {
        self.nth_str(0)
    }

    #[allow(unused)]
    pub(crate) fn current_src_str(&self) -> Spanned<&'src str> {
        let span = self.current_span();
        Spanned(self.current_str(), span)
    }

    pub(crate) fn nth_raw(&self, n: usize) -> (Token, SourceSpan) {
        if self.cursor + n >= self.lexer.len() {
            (Token::Error, SourceSpan::from((self.src.len(), 0)))
        } else {
            self.lexer[self.cursor + n]
        }
    }

    pub(crate) fn nth(&self, n: usize) -> Token {
        self.nth_raw(n).0
    }

    // TODO: Maybe we should assert end of stream when parsing scripts?
    #[allow(unused)]
    pub(crate) fn eoi(&self) -> bool {
        self.cursor >= self.lexer.len()
    }

    #[allow(unused)]
    pub(crate) fn pos(&self) -> usize {
        self.cursor
    }

    pub(crate) fn bump(&mut self) {
        self.cursor += 1
    }

    pub(crate) fn nth_matches(&self, n: usize, t: Token, s: &str) -> bool {
        self.nth(n) == t && self.nth_str(n) == s
    }

    pub(crate) fn expect_matches(&mut self, t: Token, s: &str) -> Result<&'src str, ParseError> {
        if self.nth_matches(0, t, s) {
            let s = self.current_str();
            self.bump();
            Ok(s)
        } else {
            todo!()
        }
    }

    pub(crate) fn expect(&mut self, t: Token) -> Result<&'src str, ParseError> {
        match self.current() {
            found if found == t => {
                let s = self.current_str();
                self.bump();
                Ok(s)
            }
            found => {
                let err = ParseError {
                    error: "Unrecognized token".into(),
                    src: self.src.into(),
                    err_span: self.current_span(),
                    label: Some(format!("Found {found:?} expected {t:?}")),
                    help: None,
                };
                self.errors.push(err.clone());
                self.bump();
                Err(err)
            }
        }
    }

    pub(crate) fn any<T: SmtlibParse>(&mut self) -> Result<Vec<T>, ParseError> {
        let mut res = vec![];
        while T::is_start_of(0, self) {
            res.push(T::parse(self)?);
        }
        Ok(res)
    }

    pub(crate) fn non_zero<T: SmtlibParse>(&mut self) -> Result<Vec<T>, ParseError> {
        let mut res = vec![T::parse(self)?];
        while T::is_start_of(0, self) {
            res.push(T::parse(self)?);
        }
        Ok(res)
    }

    pub(crate) fn n_plus_one<T: SmtlibParse>(&mut self) -> Result<Vec<T>, ParseError> {
        // TODO
        self.non_zero()
    }

    pub(crate) fn stuck(&self, parsing: &str) -> ParseError {
        ParseError {
            error: format!("Parser stuck while parsing {parsing:?}"),
            src: self.src.into(),
            err_span: self.current_span(),
            label: Some("The parser got stuck at this token".to_string()),
            help: None,
        }
    }
}
