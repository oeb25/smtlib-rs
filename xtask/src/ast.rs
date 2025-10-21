use color_eyre::Result;
use heck::ToPascalCase;
use indexmap::IndexMap;
use itertools::Itertools;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct RawSpec {
    #[serde(flatten)]
    general: IndexMap<String, RawSyntax>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(untagged)]
enum RawSyntax {
    Just {
        syntax: String,
        priority: Option<i32>,
        separator: Option<String>,
        response: Option<String>,
    },
    Class {
        response: Option<String>,
        #[serde(flatten)]
        cases: IndexMap<String, RawSyntax>,
    },
}

impl RawSpec {
    fn parse(&self) -> Spec {
        Spec {
            general: self
                .general
                .iter()
                .map(|(n, s)| (Name(n.clone()), s.parse()))
                .collect(),
        }
    }
}

impl RawSyntax {
    fn parse(&self) -> Syntax {
        match self {
            RawSyntax::Just {
                syntax,
                priority,
                separator,
                response,
            } => Syntax::Rule(Rule {
                syntax: parse_raw_grammar(syntax),
                priority: priority.unwrap_or_default(),
                separator: separator.clone(),
                response: response.as_ref().map(|s| parse_raw_token(s, 0)),
            }),
            RawSyntax::Class { response, cases } => Syntax::Class {
                response: response.clone().map(Into::into),
                cases: cases
                    .iter()
                    .map(|(n, s)| match s {
                        RawSyntax::Just {
                            syntax,
                            priority,
                            separator,
                            response,
                        } => (
                            n.clone(),
                            Rule {
                                syntax: parse_raw_grammar(syntax),
                                priority: priority.unwrap_or_default(),
                                separator: separator.clone(),
                                response: response.as_ref().map(|r| parse_raw_token(r, 0)),
                            },
                        ),
                        RawSyntax::Class { .. } => todo!(),
                    })
                    .collect(),
            },
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct Name(String);

impl From<String> for Name {
    fn from(value: String) -> Self {
        Name(value)
    }
}

impl Name {
    fn needs_alloc(&self, spec: &Spec) -> bool {
        match spec.general.get(self) {
            Some(Syntax::Rule(rule)) => rule.syntax.fields.iter().any(|f| match f {
                Field::One(name) => name == self,
                Field::Any(_) | Field::NonZero(_) | Field::NPlusOne(_) => false,
            }),
            Some(Syntax::Class { response: _, cases }) => cases.iter().any(|(_, case)| {
                case.syntax.fields.iter().any(|f| match f {
                    Field::One(name) => name == self,
                    Field::Any(_) | Field::NonZero(_) | Field::NPlusOne(_) => false,
                })
            }),
            None => false,
        }
    }
    fn needs_lt(&self, spec: &Spec) -> bool {
        match self.0.as_str() {
            "string" | "numeral" | "decimal" | "hexadecimal" | "binary" | "symbol" | "reserved"
            | "keyword" => true,
            "b_value" => false,
            _ => match spec.general.get(self) {
                Some(Syntax::Rule(rule)) => rule.syntax.fields.iter().any(|f| match f {
                    Field::One(name) => name.needs_lt(spec),
                    Field::Any(_) | Field::NonZero(_) | Field::NPlusOne(_) => true,
                }),
                Some(Syntax::Class { response: _, cases }) => cases.iter().any(|(_, case)| {
                    case.syntax.fields.iter().any(|f| match f {
                        Field::One(name) => name == self || name.needs_lt(spec),
                        Field::Any(_) | Field::NonZero(_) | Field::NPlusOne(_) => true,
                    })
                }),
                None => {
                    todo!(
                        "[{self:?}] missing name\noptions: \n - {}",
                        spec.general.keys().map(|n| &n.0).sorted().format("\n - ")
                    );
                }
            },
        }
    }
    fn ty(&self, _spec: &Spec) -> String {
        self.0.to_pascal_case()
    }
    fn variant(&self, spec: &Spec) -> String {
        self.ty(spec).clone()
    }
    /// With life time
    fn with_lt(&self, spec: &Spec) -> String {
        if self.needs_lt(spec) {
            format!("{}<'st>", self.ty(spec))
        } else {
            self.ty(spec)
        }
    }
    /// With anonymous life time
    fn with_alt(&self, spec: &Spec) -> String {
        if self.needs_lt(spec) {
            format!("{}<'_>", self.ty(spec))
        } else {
            self.ty(spec)
        }
    }
    fn as_smtlibparse(&self, spec: &Spec) -> String {
        match self.0.as_str() {
            "string" => "<String as SmtlibParse<'st>>".to_string(),
            _ if self.needs_lt(spec) => format!("<{}::<'st> as SmtlibParse<'st>>", self.ty(spec)),
            _ => format!("<{} as SmtlibParse<'st>>", self.ty(spec)),
        }
    }
    fn output(&self, spec: &Spec) -> String {
        match self.0.as_str() {
            "string" => "&'st str".to_string(),
            _ if self.needs_alloc(spec) => format!("&'st {}", self.with_lt(spec)),
            _ => self.with_lt(spec).to_string(),
        }
    }
}

#[derive(Debug, Clone)]
struct Spec {
    general: IndexMap<Name, Syntax>,
}

#[derive(Debug, Clone)]
struct Rule {
    syntax: Grammar,
    priority: i32,
    separator: Option<String>,
    response: Option<Token>,
}

#[derive(Debug, Clone)]
enum Syntax {
    Rule(Rule),
    Class {
        response: Option<Name>,
        cases: IndexMap<String, Rule>,
    },
}

#[derive(Debug, Clone)]
struct Grammar {
    tokens: Vec<Token>,
    fields: Vec<Field>,
}

#[derive(Debug, Clone)]
enum Token {
    LParen,
    RParen,
    Underscore,
    Annotation,
    Builtin(String),
    Reserved(String),
    Keyword(String),
    Field(usize, Field),
}

impl Token {
    pub fn is_concrete(&self) -> bool {
        use Token::*;
        match self {
            LParen | RParen | Underscore | Annotation | Keyword(_) | Builtin(_) | Reserved(_) => {
                true
            }
            Field(_, _) => false,
        }
    }
}

#[derive(Debug, Clone)]
enum Field {
    One(Name),
    Any(Name),
    NonZero(Name),
    NPlusOne(Name),
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Token::*;

        match self {
            LParen => write!(f, "("),
            RParen => write!(f, ")"),
            Underscore => write!(f, "_"),
            Annotation => write!(f, "!"),
            Builtin(s) => write!(f, "{s}"),
            Reserved(s) => write!(f, "{s}"),
            Keyword(k) => write!(f, "{k}"),
            Field(_, field) => write!(f, "{field}"),
        }
    }
}
impl std::fmt::Display for Field {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Field::One(t) => write!(f, "<{}>", t.0),
            Field::Any(t) => write!(f, "<{}>*", t.0),
            Field::NonZero(t) => write!(f, "<{}>+", t.0),
            Field::NPlusOne(t) => write!(f, "<{}>n+1", t.0),
        }
    }
}
impl std::fmt::Display for Grammar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.tokens.iter().fold("".to_string(), |mut acc, t| {
            use Token::*;
            if !acc.ends_with('(') && !acc.is_empty() {
                acc += match t {
                    RParen => "",
                    _ => " ",
                };
            }
            acc += &t.to_string();
            acc
        });
        write!(f, "{s}")
    }
}

fn parse_raw_grammar(s: &str) -> Grammar {
    let mut acc = 0;
    let p = s
        .split(' ')
        .map(|t| {
            let t = parse_raw_token(t, acc);
            if let Token::Field(_, _) = t {
                acc += 1
            }
            t
        })
        .collect_vec();
    let fields = p
        .iter()
        .filter_map(|t| match t {
            Token::Field(_, f) => Some(f.clone()),
            _ => None,
        })
        .collect();
    Grammar { tokens: p, fields }
}

fn parse_raw_token(s: &str, field_idx: usize) -> Token {
    match s {
        "(" => Token::LParen,
        ")" => Token::RParen,
        "_" => Token::Underscore,
        "!" => Token::Annotation,
        f if f.starts_with(':') => Token::Keyword(f.to_string()),
        f if f.starts_with('<') && f.ends_with('>') => {
            Token::Field(field_idx, Field::One(f[1..f.len() - 1].to_string().into()))
        }
        f if f.starts_with('<') && f.ends_with(">*") => {
            Token::Field(field_idx, Field::Any(f[1..f.len() - 2].to_string().into()))
        }
        f if f.starts_with('<') && f.ends_with(">+") => Token::Field(
            field_idx,
            Field::NonZero(f[1..f.len() - 2].to_string().into()),
        ),
        f if f.starts_with('<') && f.ends_with(">n+1") => Token::Field(
            field_idx,
            Field::NPlusOne(f[1..f.len() - 4].to_string().into()),
        ),
        f if f.chars().all(|c| c.is_alphabetic() || c == '-') => {
            if [
                "_",
                "!",
                "as",
                "BINARY",
                "DECIMAL",
                "exists",
                "forall",
                "HEXADECIMAL",
                "let",
                "match",
                "NUMERAL",
                "par",
                "STRING",
                "assert",
                "check-sat",
                "check-sat-assuming",
                "declare-const",
                "declare-datatype",
                "declare-datatypes",
                "declare-fun",
                "declare-sort",
                "define-fun",
                "define-fun-rec",
                "define-sort",
                "echo",
                "exit",
                "get-assertions",
                "get-assignment",
                "get-info",
                "get-model",
                "get-option",
                "get-proof",
                "get-unsat-assumptions",
                "get-unsat-core",
                "get-value",
                "pop",
                "push",
                "reset",
                "reset-assertions",
                "set-info",
                "set-logic",
                "set-option",
            ]
            .contains(&f)
            {
                Token::Reserved(f.to_string())
            } else {
                Token::Builtin(f.to_string())
            }
        }
        _ => todo!("{:?}", s),
    }
}

impl Syntax {
    fn rust_ty_decl_top(&self, spec: &Spec, name: &Name) -> String {
        let derive = r#"#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)] #[cfg_attr(feature = "serde", derive(serde::Serialize))]"#;
        match self {
            Syntax::Rule(r) => format!(
                "/// `{}`\n{derive}\npub struct {}({});",
                r.syntax,
                name.with_lt(spec),
                r.syntax
                    .tuple_fields(spec)
                    .map(|f| format!("pub {f}"))
                    .format(",")
            ),
            Syntax::Class { cases, .. } => format!(
                "{derive}pub enum {} {{ {} }}",
                name.with_lt(spec),
                cases
                    .iter()
                    .map(|(n, c)| c.rust_ty_decl_child(spec, n))
                    .format(", ")
            ),
        }
    }
    fn rust_display(&self, spec: &Spec, name: &Name) -> String {
        match self {
            Syntax::Rule(r) => format!(
                r#"
                impl std::fmt::Display for {} {{
                    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {{
                        {}
                    }}
                }}
                "#,
                name.with_alt(spec),
                r.rust_display_impl("self.")
            ),
            Syntax::Class { cases, .. } => format!(
                r#"
                impl std::fmt::Display for {} {{
                    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {{
                        match self {{ {} }}
                    }}
                }}
                "#,
                name.with_alt(spec),
                cases
                    .iter()
                    .map(|(n, c)| if c.syntax.fields.is_empty() {
                        format!(
                            "Self::{} => {},",
                            n.to_pascal_case(),
                            c.rust_display_impl("todo.")
                        )
                    } else {
                        format!(
                            "Self::{}({}) => {},",
                            n.to_pascal_case(),
                            c.syntax
                                .fields
                                .iter()
                                .enumerate()
                                .map(|(idx, _)| format!("m{idx}"))
                                .format(","),
                            c.rust_display_impl("m")
                        )
                    })
                    .format("\n")
            ),
        }
    }
    fn rust_parse(&self, spec: &Spec, name: &Name) -> String {
        match self {
            Syntax::Rule(r) => {
                format!(
                    "impl<'st> {} {{
                        pub fn parse(st: &'st Storage, src: &str) -> Result<{}, ParseError> {{
                            {}::parse(&mut Parser::new(st, src))
                        }}
                    }}
                    impl<'st> SmtlibParse<'st> for {} {{
                        type Output = {};
                        fn is_start_of(offset: usize, p: &mut Parser<'st, '_>) -> bool {{
                            {}
                        }}
                        fn parse(p: &mut Parser<'st, '_>) -> Result<Self::Output, ParseError> {{
                            {}
                            {}
                        }}
                    }}",
                    name.with_lt(spec),
                    name.output(spec),
                    name.as_smtlibparse(spec),
                    name.with_lt(spec),
                    name.output(spec),
                    r.rust_start_of_impl(spec),
                    r.rust_parse_impl(spec),
                    if r.syntax.fields.is_empty() {
                        "Ok(Self)".to_string()
                    } else {
                        format!(
                            "Ok(Self({}))",
                            r.syntax
                                .fields
                                .iter()
                                .enumerate()
                                .map(|(idx, _)| format!("m{idx}"))
                                .format(", ")
                        )
                    }
                )
            }
            Syntax::Class { cases, .. } => {
                let is_start_of = cases
                    .iter()
                    .sorted_by_key(|(_, c)| {
                        (
                            c.priority,
                            c.syntax.tokens.iter().filter(|t| t.is_concrete()).count(),
                        )
                    })
                    .rev()
                    .map(|(_, c)| format!("({})", c.rust_start_of_check(spec)))
                    .format(" || ");
                let parse = cases
                    .iter()
                    .sorted_by_key(|(_, c)| {
                        (
                            c.priority,
                            c.syntax.tokens.iter().filter(|t| t.is_concrete()).count(),
                        )
                    })
                    .rev()
                    .map(|(n, c)| {
                        let construct = rust_parse_construct_variant("self", n, &c.syntax);
                        let construct= if name.needs_alloc(spec) {
                            format!("p.storage.alloc({construct})")
                        } else {construct};
                        format!(
                            "if {} {{ {}\n #[allow(clippy::useless_conversion)]\nreturn Ok({construct}); }}",
                            c.rust_start_of_check(spec),
                            c.rust_parse_impl(spec),
                        )
                    })
                    .format("\n");
                format!(
                    "impl<'st> {} {{
                        pub fn parse(st: &'st Storage, src: &str) -> Result<{}, ParseError> {{
                            {}::parse(&mut Parser::new(st, src))
                        }}
                    }}
                    impl<'st> SmtlibParse<'st> for {} {{
                        type Output = {};
                        fn is_start_of(offset: usize, p: &mut Parser<'st, '_>) -> bool {{
                            {is_start_of}
                        }}
                        fn parse(p: &mut Parser<'st, '_>) -> Result<Self::Output, ParseError> {{
                            let offset = 0;
                            {parse}
                            Err(p.stuck({:?}))
                        }}
                    }}",
                    name.with_lt(spec),
                    name.output(spec),
                    name.as_smtlibparse(spec),
                    name.with_lt(spec),
                    name.output(spec),
                    name.variant(spec),
                )
            }
        }
    }
    fn rust_response(&self, spec: &Spec, name: &Name) -> String {
        match self {
            Syntax::Rule(_) | Syntax::Class { response: None, .. } => "".to_string(),
            Syntax::Class {
                cases,
                response: Some(response),
            } => {
                let has_response = cases
                    .iter()
                    .map(|(n, c)| {
                        format!(
                            "Self::{}{} => {},",
                            n.to_pascal_case(),
                            if c.syntax.fields.is_empty() {
                                "".to_string()
                            } else {
                                format!("({})", c.syntax.fields.iter().map(|_| "_").format(", "))
                            },
                            c.response.is_some(),
                        )
                    })
                    .format("\n");
                let parse_response = cases
                    .iter()
                    .map(|(n, c)| {
                        format!(
                            "Self::{}{} => {},",
                            n.to_pascal_case(),
                            if c.syntax.fields.is_empty() {
                                "".to_string()
                            } else {
                                format!("({})", c.syntax.fields.iter().map(|_| "_").format(", "))
                            },
                            if let Some(res) = &c.response {
                                let res_ty = match res {
                                    Token::LParen
                                    | Token::RParen
                                    | Token::Underscore
                                    | Token::Annotation
                                    | Token::Builtin(_)
                                    | Token::Reserved(_)
                                    | Token::Keyword(_) => todo!(),
                                    Token::Field(_, f) => match f {
                                        Field::One(t)
                                        | Field::Any(t)
                                        | Field::NonZero(t)
                                        | Field::NPlusOne(t) => t,
                                    },
                                };
                                format!(
                                    "Ok(Some({}::{}({}::parse(&mut Parser::new(st, response))?)))",
                                    response.ty(spec),
                                    res_ty.variant(spec),
                                    res_ty.as_smtlibparse(spec),
                                )
                            } else {
                                "Ok(None)".to_string()
                            },
                        )
                    })
                    .format("\n");

                format!(
                        "
                        impl<'st> {} {{
                            pub fn has_response(&self) -> bool {{
                                match self {{
                                    {}
                                }}
                            }}
                            pub fn parse_response(&self, st: &'st Storage, response: &str) -> Result<std::option::Option<{}>, ParseError> {{
                                match self {{
                                    {}
                                }}
                            }}
                        }}
                        ",
                        name.with_lt(spec),
                        has_response,
                        response.output(spec),
                        parse_response,
                    )
            }
        }
    }
}

impl Rule {
    fn rust_display_impl(&self, scope: &str) -> String {
        format!(
            r#"write!(f, "{}" {})"#,
            self.syntax
                .tokens
                .iter()
                .fold("".to_string(), |mut acc, t| {
                    use Token::*;
                    if !acc.ends_with('(') && !acc.is_empty() {
                        acc += match t {
                            RParen => "",
                            _ => " ",
                        };
                    }
                    acc += match t {
                        LParen => "(",
                        RParen => ")",
                        Underscore => "_",
                        Annotation => "!",
                        Builtin(s) => s,
                        Reserved(s) => s,
                        Keyword(k) => k,
                        Field(_, _) => "{}",
                    };
                    acc
                }),
            self.syntax
                .fields
                .iter()
                .enumerate()
                .map(|(idx, f)| match f {
                    Field::One(_) => {
                        format!(", {scope}{idx}")
                    }
                    Field::Any(_) | Field::NonZero(_) | Field::NPlusOne(_) => {
                        format!(
                            r#", {scope}{idx}.iter().format({:?})"#,
                            self.separator.as_deref().unwrap_or(" ")
                        )
                    }
                })
                .format("")
        )
    }
    fn rust_ty_decl_child(&self, spec: &Spec, name: &str) -> String {
        if self.syntax.fields.is_empty() {
            format!("/// `{}`\n{}", self.syntax, name.to_pascal_case())
        } else {
            format!(
                "/// `{}`\n{}({})",
                self.syntax,
                name.to_pascal_case(),
                self.syntax.tuple_fields(spec).format(",")
            )
        }
    }
    fn rust_start_of_check(&self, spec: &Spec) -> String {
        let is_all_variable = !self.syntax.tokens.iter().any(|t| t.is_concrete());

        if is_all_variable {
            self.syntax
                .tokens
                .iter()
                .enumerate()
                .map(|(idx, t)| rust_check_token(spec, idx, t))
                .format(" && ")
                .to_string()
        } else if !self.syntax.tokens[0].is_concrete() {
            let q = rust_check_token(spec, 0, &self.syntax.tokens[0]);
            assert!(!q.is_empty());
            q
        } else {
            self.syntax
                .tokens
                .iter()
                .take_while(|t| t.is_concrete())
                .enumerate()
                .map(|(idx, t)| rust_check_token(spec, idx, t))
                .format(" && ")
                .to_string()
        }
    }
    fn rust_start_of_impl(&self, spec: &Spec) -> String {
        self.rust_start_of_check(spec)
    }
    fn rust_parse_impl(&self, spec: &Spec) -> String {
        let stmts = self.syntax.tokens.iter().map(|t| rust_parse_token(spec, t));
        stmts.format("\n").to_string()
    }
}

fn rust_parse_construct_variant(suffix: &str, name: &str, syntax: &Grammar) -> String {
    format!(
        "{}::{}{}",
        suffix.to_pascal_case(),
        name.to_pascal_case(),
        if syntax.fields.is_empty() {
            "".to_string()
        } else {
            format!(
                "({})",
                syntax
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(idx, _)| format!("m{idx}.into()"))
                    .format(", ")
            )
        }
    )
}

fn rust_parse_token(spec: &Spec, t: &Token) -> String {
    match t {
        Token::LParen => "p.expect(Token::LParen)?;".to_string(),
        Token::RParen => "p.expect(Token::RParen)?;".to_string(),
        Token::Underscore => "p.expect_matches(Token::Reserved, \"_\")?;".to_string(),
        Token::Annotation => "p.expect_matches(Token::Reserved, \"!\")?;".to_string(),
        Token::Builtin(b) => format!("p.expect_matches(Token::Symbol, {b:?})?;"),
        Token::Reserved(b) => format!("p.expect_matches(Token::Reserved, {b:?})?;"),
        Token::Keyword(kw) => format!("p.expect_matches(Token::Keyword, {kw:?})?;"),
        Token::Field(idx, f) => match f {
            Field::One(t) => {
                format!("let m{idx} = {}::parse(p)?;", t.as_smtlibparse(spec))
            }
            Field::Any(t) => format!("let m{idx} = p.any::<{}>()?;", t.with_lt(spec)),
            Field::NonZero(t) => {
                format!("let m{idx} = p.non_zero::<{}>()?;", t.with_lt(spec))
            }
            Field::NPlusOne(t) => {
                format!("let m{idx} = p.n_plus_one::<{}>()?;", t.with_lt(spec))
            }
        },
    }
}

fn rust_check_token(spec: &Spec, idx: usize, t: &Token) -> String {
    match t {
        Token::LParen => format!("p.nth(offset + {idx}) == Token::LParen"),
        Token::RParen => format!("p.nth(offset + {idx}) == Token::RParen"),
        Token::Underscore => format!("p.nth_matches(offset + {idx}, Token::Reserved, \"_\")"),
        Token::Annotation => format!("p.nth_matches(offset + {idx}, Token::Reserved, \"!\")"),
        Token::Builtin(b) => format!("p.nth_matches(offset + {idx}, Token::Symbol, {b:?})"),
        Token::Reserved(b) => format!("p.nth_matches(offset + {idx}, Token::Reserved, {b:?})"),
        Token::Keyword(kw) => {
            format!("p.nth_matches(offset + {idx}, Token::Keyword, {kw:?})")
        }
        Token::Field(_, f) => match f {
            Field::One(t) | Field::NonZero(t) | Field::NPlusOne(t) => {
                format!("{}::is_start_of(offset + {idx}, p)", t.variant(spec))
            }
            Field::Any(_) => "todo!(\"{offset:?}, {p:?}\")".to_string(),
        },
    }
}

impl Grammar {
    fn tuple_fields<'a>(&'a self, spec: &'a Spec) -> impl Iterator<Item = String> + 'a {
        self.fields.iter().map(|f| match &f {
            Field::One(t) => t.output(spec),
            Field::Any(t) | Field::NonZero(t) | Field::NPlusOne(t) => {
                format!("&'st [{}]", t.output(spec))
            }
        })
    }
}

pub fn generate() -> Result<String> {
    use std::fmt::Write;

    let mut buf = String::new();

    let raw: RawSpec = toml::from_str(include_str!("./spec.toml"))?;
    let spec = raw.parse();

    writeln!(buf, "// This file is autogenerated! DO NOT EDIT!\n")?;
    writeln!(buf, "use crate::parse::{{Token, Parser, ParseError}};")?;
    writeln!(buf, "use crate::storage::Storage;")?;
    writeln!(buf, "use itertools::Itertools; use crate::lexicon::*;\n")?;

    for (name, s) in &spec.general {
        writeln!(buf, "{}", s.rust_ty_decl_top(&spec, name))?;
        writeln!(buf, "{}", s.rust_display(&spec, name))?;
        writeln!(buf, "{}", s.rust_parse(&spec, name))?;
        writeln!(buf, "{}", s.rust_response(&spec, name))?;
    }
    let buf = buf.replace(" + 0", "");

    let file = syn::parse_file(&buf)?;
    let pretty = prettyplease::unparse(&file);

    Ok(pretty)
}
