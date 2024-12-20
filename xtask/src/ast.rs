use std::collections::HashSet;

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
                .map(|(n, s)| (n.clone(), s.parse()))
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
            } => {
                Syntax::Rule(Rule {
                    syntax: parse_raw_grammar(syntax),
                    priority: priority.unwrap_or_default(),
                    separator: separator.clone(),
                    response: response.as_ref().map(|s| parse_raw_token(s, 0)),
                })
            }
            RawSyntax::Class { response, cases } => {
                Syntax::Class {
                    response: response.clone(),
                    cases: cases
                        .iter()
                        .map(|(n, s)| {
                            match s {
                                RawSyntax::Just {
                                    syntax,
                                    priority,
                                    separator,
                                    response,
                                } => {
                                    (n.clone(), Rule {
                                        syntax: parse_raw_grammar(syntax),
                                        priority: priority.unwrap_or_default(),
                                        separator: separator.clone(),
                                        response: response.as_ref().map(|r| parse_raw_token(r, 0)),
                                    })
                                }
                                RawSyntax::Class { .. } => todo!(),
                            }
                        })
                        .collect(),
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Spec {
    general: IndexMap<String, Syntax>,
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
        response: Option<String>,
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
            Field(..) => false,
        }
    }
}

#[derive(Debug, Clone)]
enum Field {
    One(String),
    Any(String),
    NonZero(String),
    NPlusOne(String),
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
            Field::One(t) => write!(f, "<{t}>"),
            Field::Any(t) => write!(f, "<{t}>*"),
            Field::NonZero(t) => write!(f, "<{t}>+"),
            Field::NPlusOne(t) => write!(f, "<{t}>n+1"),
        }
    }
}
impl std::fmt::Display for Grammar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.tokens.iter().fold("".to_string(), |mut acc, t| {
            use Token::*;
            if !acc.ends_with(|c| c == '(') && !acc.is_empty() {
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
            if let Token::Field(..) = t {
                acc += 1
            }
            t
        })
        .collect_vec();
    let fields = p
        .iter()
        .filter_map(|t| {
            match t {
                Token::Field(_, f) => Some(f.clone()),
                _ => None,
            }
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
            Token::Field(field_idx, Field::One(f[1..f.len() - 1].to_string()))
        }
        f if f.starts_with('<') && f.ends_with(">*") => {
            Token::Field(field_idx, Field::Any(f[1..f.len() - 2].to_string()))
        }
        f if f.starts_with('<') && f.ends_with(">+") => {
            Token::Field(field_idx, Field::NonZero(f[1..f.len() - 2].to_string()))
        }
        f if f.starts_with('<') && f.ends_with(">n+1") => {
            Token::Field(field_idx, Field::NPlusOne(f[1..f.len() - 4].to_string()))
        }
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
    fn rust_ty_decl_top(&self, name: &str) -> String {
        let derive = r#"#[derive(Debug, Clone, PartialEq, Eq, Hash)] #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]"#;
        match self {
            Syntax::Rule(r) => {
                format!(
                    "/// `{}`\n{derive}\npub struct {}({});",
                    r.syntax,
                    name.to_pascal_case(),
                    r.syntax
                        .tuple_fields(&[name.to_string()].into_iter().collect())
                        .map(|f| format!("pub {f}"))
                        .format(",")
                )
            }
            Syntax::Class { cases, .. } => {
                format!(
                    "{derive}pub enum {} {{ {} }}",
                    name.to_pascal_case(),
                    cases
                        .iter()
                        .map(|(n, c)| {
                            c.rust_ty_decl_child(n, [name.to_string()].into_iter().collect())
                        })
                        .format(", ")
                )
            }
        }
    }

    fn rust_display(&self, name: &str) -> String {
        match self {
            Syntax::Rule(r) => {
                format!(
                    r#"
                impl std::fmt::Display for {} {{
                    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {{
                        {}
                    }}
                }}
                "#,
                    name.to_pascal_case(),
                    r.rust_display_impl("self.")
                )
            }
            Syntax::Class { cases, .. } => {
                format!(
                    r#"
                impl std::fmt::Display for {} {{
                    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {{
                        match self {{ {} }}
                    }}
                }}
                "#,
                    name.to_pascal_case(),
                    cases
                        .iter()
                        .map(|(n, c)| {
                            if c.syntax.fields.is_empty() {
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
                            }
                        })
                        .format("\n")
                )
            }
        }
    }

    fn rust_parse(&self, name: &str) -> String {
        match self {
            Syntax::Rule(r) => {
                format!(
                    "impl {} {{
                        pub fn parse(src: &str) -> Result<Self, ParseError> {{
                            SmtlibParse::parse(&mut Parser::new(src))
                        }}
                    }}
                    impl SmtlibParse for {} {{
                        fn is_start_of(offset: usize, p: &mut Parser) -> bool {{
                            {}
                        }}
                        fn parse(p: &mut Parser) -> Result<Self, ParseError> {{
                            {}
                            {}
                        }}
                    }}",
                    name.to_pascal_case(),
                    name.to_pascal_case(),
                    r.rust_start_of_impl(),
                    r.rust_parse_impl(),
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
                    .map(|(_, c)| format!("({})", c.rust_start_of_check()))
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
                        format!(
                            "if {} {{ {}\n #[allow(clippy::useless_conversion)]\nreturn Ok({construct}); }}",
                            c.rust_start_of_check(),
                            c.rust_parse_impl(),
                        )
                    })
                    .format("\n");
                format!(
                    "impl {} {{
                        pub fn parse(src: &str) -> Result<Self, ParseError> {{
                            SmtlibParse::parse(&mut Parser::new(src))
                        }}
                    }}
                    impl SmtlibParse for {} {{
                        fn is_start_of(offset: usize, p: &mut Parser) -> bool {{
                            {is_start_of}
                        }}
                        fn parse(p: &mut Parser) -> Result<Self, ParseError> {{
                            let offset = 0;
                            {parse}
                            Err(p.stuck({name:?}))
                        }}
                    }}",
                    name.to_pascal_case(),
                    name.to_pascal_case(),
                )
            }
        }
    }

    fn rust_response(&self, name: &str) -> String {
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
                                    Token::Field(_, f) => {
                                        match f {
                                            Field::One(t)
                                            | Field::Any(t)
                                            | Field::NonZero(t)
                                            | Field::NPlusOne(t) => t.to_string(),
                                        }
                                    }
                                };
                                format!(
                                    "Ok(Some({}::{}({}::parse(response)?)))",
                                    response.to_pascal_case(),
                                    res_ty.to_pascal_case(),
                                    res_ty.to_pascal_case(),
                                )
                            } else {
                                "Ok(None)".to_string()
                            },
                        )
                    })
                    .format("\n");

                format!(
                        "
                        impl {} {{
                            pub fn has_response(&self) -> bool {{
                                match self {{
                                    {}
                                }}
                            }}
                            pub fn parse_response(&self, response: &str) -> Result<std::option::Option<{}>, ParseError> {{
                                match self {{
                                    {}
                                }}
                            }}
                        }}
                        ",
                        name.to_pascal_case(),
                        has_response,
                        response.to_pascal_case(),
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
                    if !acc.ends_with(|c| c == '(') && !acc.is_empty() {
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
                        Field(..) => "{}",
                    };
                    acc
                }),
            self.syntax
                .fields
                .iter()
                .enumerate()
                .map(|(idx, f)| {
                    match f {
                        Field::One(_) => {
                            format!(", {scope}{idx}")
                        }
                        Field::Any(_) | Field::NonZero(_) | Field::NPlusOne(_) => {
                            format!(
                                r#", {scope}{idx}.iter().format({:?})"#,
                                self.separator.as_deref().unwrap_or(" ")
                            )
                        }
                    }
                })
                .format("")
        )
    }

    fn rust_ty_decl_child(&self, name: &str, inside_of: HashSet<String>) -> String {
        if self.syntax.fields.is_empty() {
            format!("/// `{}`\n{}", self.syntax, name.to_pascal_case())
        } else {
            format!(
                "/// `{}`\n{}({})",
                self.syntax,
                name.to_pascal_case(),
                self.syntax.tuple_fields(&inside_of).format(",")
            )
        }
    }

    fn rust_start_of_check(&self) -> String {
        let is_all_variable = !self.syntax.tokens.iter().any(|t| t.is_concrete());

        if is_all_variable {
            self.syntax
                .tokens
                .iter()
                .enumerate()
                .map(|(idx, t)| rust_check_token(idx, t))
                .format(" && ")
                .to_string()
        } else if !self.syntax.tokens[0].is_concrete() {
            let q = rust_check_token(0, &self.syntax.tokens[0]);
            assert!(!q.is_empty());
            q
        } else {
            self.syntax
                .tokens
                .iter()
                .take_while(|t| t.is_concrete())
                .enumerate()
                .map(|(idx, t)| rust_check_token(idx, t))
                .format(" && ")
                .to_string()
        }
    }

    fn rust_start_of_impl(&self) -> String {
        self.rust_start_of_check()
    }

    fn rust_parse_impl(&self) -> String {
        let stmts = self.syntax.tokens.iter().map(rust_parse_token);
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

fn rust_parse_token(t: &Token) -> String {
    match t {
        Token::LParen => "p.expect(Token::LParen)?;".to_string(),
        Token::RParen => "p.expect(Token::RParen)?;".to_string(),
        Token::Underscore => "p.expect_matches(Token::Reserved, \"_\")?;".to_string(),
        Token::Annotation => "p.expect_matches(Token::Reserved, \"!\")?;".to_string(),
        Token::Builtin(b) => format!("p.expect_matches(Token::Symbol, {b:?})?;"),
        Token::Reserved(b) => format!("p.expect_matches(Token::Reserved, {b:?})?;"),
        Token::Keyword(kw) => format!("p.expect_matches(Token::Keyword, {kw:?})?;"),
        Token::Field(idx, f) => {
            match f {
                Field::One(t) => {
                    format!(
                        "let m{idx} = <{} as SmtlibParse>::parse(p)?;",
                        t.to_pascal_case()
                    )
                }
                Field::Any(t) => format!("let m{idx} = p.any::<{}>()?;", t.to_pascal_case()),
                Field::NonZero(t) => {
                    format!("let m{idx} = p.non_zero::<{}>()?;", t.to_pascal_case())
                }
                Field::NPlusOne(t) => {
                    format!("let m{idx} = p.n_plus_one::<{}>()?;", t.to_pascal_case())
                }
            }
        }
    }
}

fn rust_check_token(idx: usize, t: &Token) -> String {
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
        Token::Field(_, f) => {
            match f {
                Field::One(t) | Field::NonZero(t) | Field::NPlusOne(t) => {
                    format!("{}::is_start_of(offset + {idx}, p)", t.to_pascal_case())
                }
                Field::Any(_) => "todo!(\"{offset:?}, {p:?}\")".to_string(),
            }
        }
    }
}

impl Grammar {
    fn tuple_fields<'a>(
        &'a self,
        inside_of: &'a HashSet<String>,
    ) -> impl Iterator<Item = String> + 'a {
        self.fields.iter().map(|f| {
            match &f {
                Field::One(t) => {
                    if inside_of.contains(t) {
                        format!("Box<{}>", t.to_pascal_case())
                    } else {
                        t.to_pascal_case()
                    }
                }
                Field::Any(t) | Field::NonZero(t) | Field::NPlusOne(t) => {
                    format!("Vec<{}>", t.to_pascal_case())
                }
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
    writeln!(buf, "use itertools::Itertools; use crate::lexicon::*;\n")?;

    for (name, s) in &spec.general {
        writeln!(buf, "{}", s.rust_ty_decl_top(name))?;
        writeln!(buf, "{}", s.rust_display(name))?;
        writeln!(buf, "{}", s.rust_parse(name))?;
        writeln!(buf, "{}", s.rust_response(name))?;
    }
    let buf = buf.replace(" + 0", "");

    let file = syn::parse_file(&buf)?;
    let pretty = prettyplease::unparse(&file);

    Ok(pretty)
}
