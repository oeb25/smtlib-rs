// TODO: This does not currently work

use itertools::Itertools;
use miette::IntoDiagnostic;
use smtlib::{
    BitVec, SatResultWithModel, Solver, and,
    backend::{Backend, cvc5_binary::Cvc5Binary, z3_binary::Z3Binary},
    distinct, or,
    prelude::*,
};

fn queens<B: Backend>(backend: B) -> miette::Result<()> {
    let x0 = BitVec::<4>::new_const("x0");
    let x1 = BitVec::<4>::new_const("x1");
    let x2 = BitVec::<4>::new_const("x2");
    let x3 = BitVec::<4>::new_const("x3");
    let x4 = BitVec::<4>::new_const("x4");
    let x5 = BitVec::<4>::new_const("x5");
    let x6 = BitVec::<4>::new_const("x6");
    let x7 = BitVec::<4>::new_const("x7");
    let xs = [x0, x1, x2, x3, x4, x5, x6, x7];

    let mut solver = Solver::new(backend)?;

    // solver.set_logic(Logic::QF_BV)?;

    dbg!(BitVec::<4>::from(8));

    solver.assert(and([
        x0._eq(BitVec::from(8) % x0),
        // x1._eq(x1 % 8),
        // x2._eq(x2 % 8),
        // x3._eq(x3 % 8),
        // x4._eq(x4 % 8),
        // x5._eq(x5 % 8),
        // x6._eq(x6 % 8),
        // x7._eq(x7 % 8),
    ]))?;

    // solver.assert(distinct(xs))?;

    // solver.assert(distinct([
    //     (x0 + (8 - 0)) % 8,
    //     (x1 + (8 - 1)) % 8,
    //     (x2 + (8 - 2)) % 8,
    //     (x3 + (8 - 3)) % 8,
    //     (x4 + (8 - 4)) % 8,
    //     (x5 + (8 - 5)) % 8,
    //     (x6 + (8 - 6)) % 8,
    //     (x7 + (8 - 7)) % 8,
    // ]))?;

    for i in 1.. {
        match solver.check_sat_with_model()? {
            SatResultWithModel::Unsat => {
                eprintln!("No more solutions!");
                break;
            }
            SatResultWithModel::Sat(model) => {
                println!(
                    "{i:5}: {}",
                    xs.map(|x| model.eval(x).map(|x| x.to_string()).unwrap_or_default())
                        .iter()
                        .format(",")
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
