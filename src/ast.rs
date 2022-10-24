use std::{collections::HashSet, fmt::Display};

use itertools::Itertools;

pub type PropLiteral = ();
pub type Numeral = ();
pub type Decimal = ();
pub type Hexadecimal = ();
pub type Binary = ();

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Symbol(pub String);
impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionDef(pub Symbol, pub Vec<SortedVar>, pub Sort);
impl Display for FunctionDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} ({}) {})", self.0, self.1.iter().format(" "), self.2)
    }
}

pub type FunctionDec = ();
pub type DatatypeDec = ();
pub type SortDec = ();
pub type InfoFlag = ();
pub type Keyword = ();

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Index {
    Numeral(Numeral),
    Symbol(Symbol),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Identifier {
    // Symbol
    Simple(Symbol),
    // (_ Symbol Index+)
    Indexed(Symbol, Vec<Index>),
}
impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Identifier::Simple(s) => write!(f, "{s}"),
            Identifier::Indexed(_, _) => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AttributeValue {
    SpecConstant(SpecConstant),
    Symbol(Symbol),
    SExprs(Vec<SExpr>),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Attribute(pub Keyword, pub std::option::Option<AttributeValue>);
impl Display for Attribute {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort(pub Identifier, pub Vec<Sort>);
impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.1.is_empty() {
            write!(f, "{}", self.0)
        } else {
            todo!()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SpecConstant {
    Numeral(Numeral),
    Decimal(Decimal),
    Hexadecimal(Hexadecimal),
    Binary(Binary),
    String(String),
}
impl Display for SpecConstant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SExpr {
    SpecConstant,
    Symbol,
    Reserved,
    Keyword,
    List(Vec<SExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QualIdentifier(pub Identifier, pub std::option::Option<Sort>);
impl Display for QualIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(s) = &self.1 {
            write!(f, "(as {} {s})", self.0)
        } else {
            write!(f, "{}", self.0)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarBinding(pub Symbol, pub Term);
impl Display for VarBinding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SortedVar(pub Symbol, pub Sort);
impl Display for SortedVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {})", self.0, self.1)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Pattern(pub Symbol, pub Vec<Symbol>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MatchCase(pub Pattern, pub Term);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    // <spec_constant>
    SpecConstant(SpecConstant),
    // QualIdentifier
    // (QualIdentifier Term+)
    QualIdentifier(QualIdentifier, Vec<Term>),
    // (let <var_binding>* <term>)
    Let(Vec<VarBinding>, Box<Term>),
    // (forall <sorted_var>+ <term>)
    Forall(Vec<SortedVar>, Box<Term>),
    // (exists <sorted_var>+ <term>)
    Exists(Vec<SortedVar>, Box<Term>),
    // (match <term> <match_case>+)
    Match(Box<Term>, Vec<MatchCase>),
    // (! <term> <attribute>+)
    Bang,
}
impl Term {
    pub(crate) fn all_consts(&self) -> HashSet<&QualIdentifier> {
        match self {
            Term::SpecConstant(_) => HashSet::new(),
            Term::QualIdentifier(q, args) => std::iter::once(q)
                .chain(args.iter().flat_map(|arg| arg.all_consts()))
                .collect(),
            Term::Let(_, _) => todo!(),
            Term::Forall(_, _) => todo!(),
            Term::Exists(_, _) => todo!(),
            Term::Match(_, _) => todo!(),
            Term::Bang => todo!(),
        }
    }
    pub(crate) fn strip_sort(self) -> Term {
        match self {
            Term::SpecConstant(_) => self,
            Term::QualIdentifier(QualIdentifier(ident, _), args) => Term::QualIdentifier(
                QualIdentifier(ident, None),
                args.into_iter().map(|arg| arg.strip_sort()).collect(),
            ),
            Term::Let(_, _) => todo!(),
            Term::Forall(_, _) => todo!(),
            Term::Exists(_, _) => todo!(),
            Term::Match(_, _) => todo!(),
            Term::Bang => todo!(),
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::SpecConstant(c) => write!(f, "{c}"),
            Term::QualIdentifier(q, ts) => {
                if ts.is_empty() {
                    write!(f, "{q}")
                } else {
                    write!(f, "({q} {})", ts.iter().format(" "))
                }
            }
            Term::Let(bs, t) => write!(f, "(let ({}) {t})", bs.iter().format(" ")),
            Term::Forall(vars, t) => write!(f, "(forall ({}) {t})", vars.iter().format(" ")),
            Term::Exists(vars, t) => write!(f, "(exists ({}) {t})", vars.iter().format(" ")),
            Term::Match(_, _) => write!(f, "(match)"),
            Term::Bang => write!(f, "!"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Command {
    // (assert Term)
    Assert(Term),
    // (check-sat)
    CheckSat,
    // (check-sat-assuming <prop_literal>*)
    CheckSatAssuming(Vec<PropLiteral>),
    // (declare-const Symbol Sort)
    DeclareConst(Symbol, Sort),
    // (declare-datatype Symbol DatatypeDec)
    DeclareDatatype(Symbol, DatatypeDec),
    // (declare-datatypes SortDec n+1 DatatypeDec n+1)
    DeclareDatatypes(Vec<SortDec>, Vec<DatatypeDec>),
    // (declare-fun Symbol Sort∗ Sort)
    DeclareFun(Symbol, Vec<Sort>, Sort),
    // (declare-sort Symbol Numeral)
    DeclareSort(Symbol, Numeral),
    // (define-fun FunctionDef)
    DefineFun(FunctionDef),
    // (define-fun-rec FunctionDef)
    DefineFunRec(FunctionDef),
    // (define-funs-rec FunctionDec n+1 Termn+1)
    DefineFunsRec(Vec<FunctionDec>, Vec<Term>),
    // (define-sort Symbol Symbol∗ Sort)
    DefineSort(Symbol, Vec<Symbol>, Sort),
    // (echo String)
    Echo(String),
    // (exit)
    Exit,
    // (get-assertions)
    GetAssertions,
    // (get-assignment)
    GetAssignment,
    // (get-info <info_flag>)
    GetInfo(InfoFlag),
    // (get-model)
    GetModel,
    // (get-option Keyword)
    GetOption(Keyword),
    // (get-proof)
    GetProof,
    // (get-unsat-assumptions)
    GetUnsatAssumptions,
    // (get-unsat-core)
    GetUnsatCore,
    // (get-value Term+)
    GetValue(Vec<Term>),
    // (pop Numeral)
    Pop(Numeral),
    // (push Numeral)
    Push(Numeral),
    // (reset)
    Reset,
    // (reset-assertions)
    ResetAssertions,
    // (set-info Attribute)
    SetInfo(Attribute),
    // (set-logic Symbol)
    SetLogic(Symbol),
    // (set-option <option>)
    SetOption(Option),
}
impl std::fmt::Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Command::Assert(t) => write!(f, "(assert {t})"),
            Command::CheckSat => write!(f, "(check-sat)"),
            Command::CheckSatAssuming(pl) => {
                todo!()
                // write!(f, "(check-sat-assuming {})", pl.iter().format(" "))
            }
            Command::DeclareConst(sym, sort) => write!(f, "(declare-const {sym} {sort})"),
            Command::DeclareDatatype(sym, DatatypeDec) => {
                write!(f, "(declare-datatype Symbol DatatypeDec)")
            }
            Command::DeclareDatatypes(_, _) => {
                write!(f, "(declare-datatypes SortDec n+1 DatatypeDec n+1)")
            }
            Command::DeclareFun(sym, _, sort) => write!(f, "(declare-fun Symbol Sort∗ {sort})"),
            Command::DeclareSort(sym, Numeral) => write!(f, "(declare-sort Symbol Numeral)"),
            Command::DefineFun(def) => write!(f, "(define-fun {def})"),
            Command::DefineFunRec(def) => write!(f, "(define-fun-rec {def})"),
            Command::DefineFunsRec(_, _) => write!(f, "(define-funs-rec FunctionDec n+1 Termn+1)"),
            Command::DefineSort(sym, _, sort) => write!(f, "(define-sort Symbol Symbol∗ {sort})"),
            Command::Echo(String) => write!(f, "(echo String)"),
            Command::Exit => write!(f, "(exit)"),
            Command::GetAssertions => write!(f, "(get-assertions)"),
            Command::GetAssignment => write!(f, "(get-assignment)"),
            Command::GetInfo(InfoFlag) => write!(f, "(get-info <info_flag>)"),
            Command::GetModel => write!(f, "(get-model)"),
            Command::GetOption(Keyword) => write!(f, "(get-option Keyword)"),
            Command::GetProof => write!(f, "(get-proof)"),
            Command::GetUnsatAssumptions => write!(f, "(get-unsat-assumptions)"),
            Command::GetUnsatCore => write!(f, "(get-unsat-core)"),
            Command::GetValue(_) => write!(f, "(get-value Term+)"),
            Command::Pop(Numeral) => write!(f, "(pop Numeral)"),
            Command::Push(Numeral) => write!(f, "(push Numeral)"),
            Command::Reset => write!(f, "(reset)"),
            Command::ResetAssertions => write!(f, "(reset-assertions)"),
            Command::SetInfo(attr) => write!(f, "(set-info {attr})"),
            Command::SetLogic(sym) => write!(f, "(set-logic Symbol)"),
            Command::SetOption(Option) => write!(f, "(set-option <option>)"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Script(pub Vec<Command>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Option {
    DiagnosticOutputChannel(String),
    GlobalDeclarations(bool),
    InteractiveMode(bool),
    PrintSuccess(bool),
    ProduceAssertions(bool),
    ProduceAssignments(bool),
    ProduceModels(bool),
    ProduceProofs(bool),
    ProduceUnsatAssumptions(bool),
    ProduceUnsatCores(bool),
    RandomSeed(Numeral),
    RegularOutputChannel(String),
    ReproducibleResourceLimit(Numeral),
    Verbosity(Numeral),
    Attribute(Attribute),
}
