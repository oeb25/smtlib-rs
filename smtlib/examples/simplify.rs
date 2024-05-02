use miette::IntoDiagnostic;
use smtlib::Sort;

#[derive(Debug, Clone)]
enum Expr {
    Num(i64),
    Var(String),
    Bool(bool),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    Neq(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    Leq(Box<Expr>, Box<Expr>),
    Gt(Box<Expr>, Box<Expr>),
    Geq(Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    Neg(Box<Expr>),
}

fn parse_expr(src: &str) -> (Expr, &str) {
    let src = src.trim();
    match src.chars().next().unwrap() {
        '(' => {
            let src = &src[1..];
            let (op, src) = src.split_once(' ').unwrap();
            let (expr, src) = match op {
                "+" => binop(src, Expr::Add),
                "-" => binop(src, Expr::Sub),
                "*" => binop(src, Expr::Mul),
                "/" => binop(src, Expr::Div),
                "=" => binop(src, Expr::Eq),
                "!=" => binop(src, Expr::Neq),
                "<" => binop(src, Expr::Lt),
                "<=" => binop(src, Expr::Leq),
                ">" => binop(src, Expr::Gt),
                ">=" => binop(src, Expr::Geq),
                "&" => binop(src, Expr::And),
                "|" => binop(src, Expr::Or),
                "not" => {
                    let (e, src) = parse_expr(src);
                    (Expr::Not(Box::new(e)), src)
                }
                "neg" => {
                    let (e, src) = parse_expr(src);
                    (Expr::Neg(Box::new(e)), src)
                }
                op => todo!("unknown op: {op:?}"),
            };
            assert!(
                src.starts_with(')'),
                "expected closing paren, found {src:?}"
            );
            (expr, &src[1..])
        }
        '0'..='9' => {
            // split at the first non-digit
            let idx = src.find(|c: char| !c.is_ascii_digit()).unwrap_or(src.len());
            let (num, src) = src.split_at(idx);
            (Expr::Num(num.parse().unwrap()), src)
        }
        'a'..='z' | 'A'..='Z' => {
            // split at the first non-alphanumeric
            let idx = src
                .find(|c: char| !c.is_ascii_alphanumeric())
                .unwrap_or(src.len());
            let (var, src) = src.split_at(idx);
            let expr = match var {
                "true" => Expr::Bool(true),
                "false" => Expr::Bool(false),
                _ => Expr::Var(var.to_string()),
            };
            (expr, src)
        }
        x => todo!("{x:?}"),
    }
}

fn binop<F>(src: &str, f: F) -> (Expr, &str)
where
    F: FnOnce(Box<Expr>, Box<Expr>) -> Expr,
{
    let (lhs, src) = parse_expr(src);
    let (rhs, src) = parse_expr(src);
    (f(Box::new(lhs), Box::new(rhs)), src)
}

fn expr_to_smt_int(expr: &Expr) -> smtlib::Int {
    smtlib::Int::from_dynamic(expr_to_smt(expr))
}
fn expr_to_smt_bool(expr: &Expr) -> smtlib::Bool {
    smtlib::Bool::from_dynamic(expr_to_smt(expr))
}
fn expr_to_smt(expr: &Expr) -> smtlib::terms::Dynamic {
    match expr {
        Expr::Num(n) => smtlib::Int::from(*n).into(),
        Expr::Var(v) => smtlib::Int::from_name(v).into(),
        Expr::Bool(b) => smtlib::Bool::from(*b).into(),
        Expr::Add(l, r) => (expr_to_smt_int(l) + expr_to_smt_int(r)).into(),
        Expr::Sub(l, r) => (expr_to_smt_int(l) - expr_to_smt_int(r)).into(),
        Expr::Mul(l, r) => (expr_to_smt_int(l) * expr_to_smt_int(r)).into(),
        Expr::Div(l, r) => (expr_to_smt_int(l) / expr_to_smt_int(r)).into(),
        Expr::Eq(l, r) => expr_to_smt(l)._eq(expr_to_smt(r)).into(),
        Expr::Neq(l, r) => expr_to_smt(l)._neq(expr_to_smt(r)).into(),
        Expr::Lt(l, r) => expr_to_smt_int(l).lt(expr_to_smt_int(r)).into(),
        Expr::Leq(l, r) => expr_to_smt_int(l).le(expr_to_smt_int(r)).into(),
        Expr::Gt(l, r) => expr_to_smt_int(l).gt(expr_to_smt_int(r)).into(),
        Expr::Geq(l, r) => expr_to_smt_int(l).ge(expr_to_smt_int(r)).into(),
        Expr::And(l, r) => (expr_to_smt_bool(l) & expr_to_smt_bool(r)).into(),
        Expr::Or(l, r) => (expr_to_smt_bool(l) | expr_to_smt_bool(r)).into(),
        Expr::Not(e) => (!expr_to_smt_bool(e)).into(),
        Expr::Neg(e) => (-expr_to_smt_int(e)).into(),
    }
}

fn smt_to_expr(sexpr: &smtlib_lowlevel::ast::Term) -> Expr {
    match sexpr {
        smtlib_lowlevel::ast::Term::SpecConstant(smtlib_lowlevel::ast::SpecConstant::Numeral(
            n,
        )) => Expr::Num(n.0.parse().unwrap()),
        smtlib_lowlevel::ast::Term::Identifier(
            smtlib_lowlevel::ast::QualIdentifier::Identifier(
                smtlib_lowlevel::ast::Identifier::Simple(s),
            ),
        ) => Expr::Var(s.to_string()),
        smtlib_lowlevel::ast::Term::Application(
            smtlib_lowlevel::ast::QualIdentifier::Identifier(
                smtlib_lowlevel::ast::Identifier::Simple(s),
            ),
            args,
        ) => {
            let args = args.iter().map(smt_to_expr).collect::<Vec<_>>();
            match s.0.as_str() {
                "+" => Expr::Add(Box::new(args[0].clone()), Box::new(args[1].clone())),
                "-" => Expr::Sub(Box::new(args[0].clone()), Box::new(args[1].clone())),
                "*" => Expr::Mul(Box::new(args[0].clone()), Box::new(args[1].clone())),
                "/" => Expr::Div(Box::new(args[0].clone()), Box::new(args[1].clone())),
                "=" => Expr::Eq(Box::new(args[0].clone()), Box::new(args[1].clone())),
                "distinct" => Expr::Neq(Box::new(args[0].clone()), Box::new(args[1].clone())),
                ">" => Expr::Gt(Box::new(args[0].clone()), Box::new(args[1].clone())),
                ">=" => Expr::Geq(Box::new(args[0].clone()), Box::new(args[1].clone())),
                "<" => Expr::Lt(Box::new(args[0].clone()), Box::new(args[1].clone())),
                "<=" => Expr::Leq(Box::new(args[0].clone()), Box::new(args[1].clone())),
                "and" => Expr::And(Box::new(args[0].clone()), Box::new(args[1].clone())),
                "or" => Expr::Or(Box::new(args[0].clone()), Box::new(args[1].clone())),
                "not" => Expr::Not(Box::new(args[0].clone())),
                "neg" => Expr::Neg(Box::new(args[0].clone())),
                s => todo!("{s:?}"),
            }
        }
        s => todo!("{s:?}"),
    }
}

fn main() -> miette::Result<()> {
    miette::set_panic_hook();

    let src = std::env::args()
        .nth(1)
        .ok_or_else(|| miette::miette!("missing src"))?;

    let (expr, _) = parse_expr(&src);
    let smt = expr_to_smt(&expr);

    let mut solver =
        smtlib::Solver::new(smtlib::backend::z3_binary::Z3Binary::new("z3").into_diagnostic()?)?;

    let sexpr = solver.simplify(smt)?;
    let s = smt_to_expr(&sexpr);
    eprintln!("{s:?}");

    Ok(())
}
