// TODO: This does not currently work

use itertools::Itertools;
use miette::IntoDiagnostic;
use smtlib::{
    BitVec, Logic, SatResultWithModel, Solver, and,
    backend::{Backend, cvc5_binary::Cvc5Binary, z3_binary::Z3Binary},
    distinct, or,
    prelude::*,
};

fn queens<B: Backend>(backend: B) -> miette::Result<()> {
    let x0 = BitVec::<8>::new_const("x0");
    let x1 = BitVec::<8>::new_const("x1");
    let x2 = BitVec::<8>::new_const("x2");
    let x3 = BitVec::<8>::new_const("x3");
    let x4 = BitVec::<8>::new_const("x4");
    let x5 = BitVec::<8>::new_const("x5");
    let x6 = BitVec::<8>::new_const("x6");
    let x7 = BitVec::<8>::new_const("x7");
    let xs = [x0, x1, x2, x3, x4, x5, x6, x7];

    let mut solver = Solver::new(backend)?;

    solver.set_logic(Logic::QF_BV)?;

    solver.assert(distinct(xs))?;

    solver.assert(and([
        // 0
        (x0 & x1)._eq(0),
        (x0 & x2)._eq(0),
        (x0 & x3)._eq(0),
        (x0 & x4)._eq(0),
        (x0 & x5)._eq(0),
        (x0 & x6)._eq(0),
        (x0 & x7)._eq(0),
        // 1
        (x1 & x2)._eq(0),
        (x1 & x3)._eq(0),
        (x1 & x4)._eq(0),
        (x1 & x5)._eq(0),
        (x1 & x6)._eq(0),
        (x1 & x7)._eq(0),
        // 2
        (x2 & x3)._eq(0),
        (x2 & x4)._eq(0),
        (x2 & x5)._eq(0),
        (x2 & x6)._eq(0),
        (x2 & x7)._eq(0),
        // 3
        (x3 & x4)._eq(0),
        (x3 & x5)._eq(0),
        (x3 & x6)._eq(0),
        (x3 & x7)._eq(0),
        // 4
        (x4 & x5)._eq(0),
        (x4 & x6)._eq(0),
        (x4 & x7)._eq(0),
        // 5
        (x5 & x6)._eq(0),
        (x5 & x7)._eq(0),
        // 6
        (x6 & x7)._eq(0),
    ]))?;

    solver.assert((x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7)._eq(0b11111111))?;

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

                solver.assert(or(xs.map(|x| distinct([x.into(), model.eval(x).unwrap()]))))?;
            }
            SatResultWithModel::Unknown => todo!(),
        }
    }

    Ok(())
}

fn main() -> miette::Result<()> {
    miette::set_panic_hook();

    match std::env::args().nth(1).as_deref().unwrap_or("z3") {
        "z3" => queens(Z3Binary::new("z3").into_diagnostic()?)?,
        "cvc5" => queens(Cvc5Binary::new("cvc5").into_diagnostic()?)?,
        given => {
            miette::bail!(
                "Invalid backend: '{}'. Available backends are: 'z3', 'cvc5'",
                given
            )
        }
    }

    Ok(())
}
