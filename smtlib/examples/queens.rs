use itertools::Itertools;
use miette::IntoDiagnostic;
#[cfg(feature = "z3-static")]
use smtlib::backend::Z3Static;
use smtlib::{
    and,
    backend::{cvc5_binary::Cvc5Binary, z3_binary::Z3Binary, Backend},
    distinct, or,
    prelude::*,
    Int, Logic, SatResultWithModel, Solver, Storage,
};

fn queens<B: Backend>(st: &Storage, backend: B) -> miette::Result<()> {
    let x0 = Int::new_const(st, "x0");
    let x1 = Int::new_const(st, "x1");
    let x2 = Int::new_const(st, "x2");
    let x3 = Int::new_const(st, "x3");
    let x4 = Int::new_const(st, "x4");
    let x5 = Int::new_const(st, "x5");
    let x6 = Int::new_const(st, "x6");
    let x7 = Int::new_const(st, "x7");
    let xs = [x0, x1, x2, x3, x4, x5, x6, x7];

    let n = Int::new_const(st, "N");

    let mut solver = Solver::new(st, backend)?;

    solver.set_logic(Logic::QF_IDL)?;

    solver.assert(n._eq(8))?;

    solver.assert(and(
        st,
        [
            and(st, [x0.ge(0), x0.lt(n)]),
            and(st, [x1.ge(0), x1.lt(n)]),
            and(st, [x2.ge(0), x2.lt(n)]),
            and(st, [x3.ge(0), x3.lt(n)]),
            and(st, [x4.ge(0), x4.lt(n)]),
            and(st, [x5.ge(0), x5.lt(n)]),
            and(st, [x6.ge(0), x6.lt(n)]),
            and(st, [x7.ge(0), x7.lt(n)]),
        ],
    ))?;

    solver.assert(distinct(st, xs))?;

    solver.assert(distinct(
        st,
        [
            x0 - 0,
            x1 - 1,
            x2 - 2,
            x3 - 3,
            x4 - 4,
            x5 - 5,
            x6 - 6,
            x7 - 7,
        ],
    ))?;

    for i in 1.. {
        match solver.check_sat_with_model()? {
            SatResultWithModel::Unsat => {
                eprintln!("No more solutions!");
                break;
            }
            SatResultWithModel::Sat(model) => {
                println!(
                    "{i:5}: {}",
                    xs.map(|x| model.eval(x).unwrap()).iter().format(",")
                );

                solver.assert(or(
                    st,
                    xs.map(|x| distinct(st, [x.into(), model.eval(x).unwrap()])),
                ))?;
            }
            SatResultWithModel::Unknown => todo!(),
        }
    }

    Ok(())
}

fn main() -> miette::Result<()> {
    miette::set_panic_hook();

    let st = Storage::new();

    match std::env::args().nth(1).as_deref().unwrap_or("z3") {
        "z3" => queens(&st, Z3Binary::new("z3").into_diagnostic()?)?,
        #[cfg(feature = "z3-static")]
        "z3-static" => queens(&st, Z3Static::new().into_diagnostic()?)?,
        "cvc5" => queens(&st, Cvc5Binary::new("cvc5").into_diagnostic()?)?,
        given => miette::bail!(
            "Invalid backend: '{}'. Available backends are: 'z3', 'z3-static', 'cvc5'",
            given
        ),
    }

    Ok(())
}
