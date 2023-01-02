use itertools::Itertools;
use miette::IntoDiagnostic;
use smtlib::{
    and,
    backend::{Cvc5Binary, Z3Binary},
    distinct, or,
    terms::Sort,
    Backend, Int, Logic, SatResult, Solver,
};

fn queens<B: Backend>(backend: B) -> miette::Result<()> {
    let x0 = Int::from_name("x0");
    let x1 = Int::from_name("x1");
    let x2 = Int::from_name("x2");
    let x3 = Int::from_name("x3");
    let x4 = Int::from_name("x4");
    let x5 = Int::from_name("x5");
    let x6 = Int::from_name("x6");
    let x7 = Int::from_name("x7");
    let xs = [x0, x1, x2, x3, x4, x5, x6, x7];

    let n = Int::from_name("N");

    let mut solver = Solver::new(backend)?;

    solver.set_logic(Logic::QF_IDL)?;

    solver.assert(n._eq(8))?;

    solver.assert(and([
        and([x0.ge(0), x0.lt(n)]),
        and([x1.ge(0), x1.lt(n)]),
        and([x2.ge(0), x2.lt(n)]),
        and([x3.ge(0), x3.lt(n)]),
        and([x4.ge(0), x4.lt(n)]),
        and([x5.ge(0), x5.lt(n)]),
        and([x6.ge(0), x6.lt(n)]),
        and([x7.ge(0), x7.lt(n)]),
    ]))?;

    solver.assert(distinct(xs))?;

    solver.assert(distinct([
        x0 - 0,
        x1 - 1,
        x2 - 2,
        x3 - 3,
        x4 - 4,
        x5 - 5,
        x6 - 6,
        x7 - 7,
    ]))?;

    for i in 1.. {
        match solver.check_sat()? {
            SatResult::Unsat => {
                eprintln!("No more solutions!");
                break;
            }
            SatResult::Sat => {
                let model = solver.get_model()?;
                println!(
                    "{i:5}: {}",
                    xs.map(|x| model.eval(x).unwrap()).iter().format(",")
                );

                solver.assert(or(xs.map(|x| distinct([x.into(), model.eval(x).unwrap()]))))?;
            }
            SatResult::Unknown => todo!(),
        }
    }

    Ok(())
}

fn main() -> miette::Result<()> {
    miette::set_panic_hook();

    match std::env::args().nth(1).as_deref().unwrap_or("z3") {
        "z3" => queens(Z3Binary::new("z3").into_diagnostic()?)?,
        "cvc5" => queens(Cvc5Binary::new("cvc5").into_diagnostic()?)?,
        given => miette::bail!(
            "Invalid backend: '{}'. Available backends are: 'z3', 'cvc5'",
            given
        ),
    }

    Ok(())
}
