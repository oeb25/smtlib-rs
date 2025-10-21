use terms::StaticSorted;

use super::*;
use crate::terms::{forall, Sorted};

#[test]
fn int_math() {
    let st = Storage::new();
    let x = Int::new_const(&st, "x");
    let y = Int::new_const(&st, "hello");
    // let x_named = x.labeled();
    let mut z = 12 + y * 4;
    z += 3;
    let w = x * x + z;
    println!("{w}");
}

#[test]
fn quantifiers() {
    let st = Storage::new();
    let x = Int::new_const(&st, "x");
    let y = Int::new_const(&st, "y");

    let res = forall(&st, (x, y), (x + 2)._eq(y));
    println!("{}", res.sterm());
}

#[test]
fn negative_numbers() {
    let st = Storage::new();
    let mut solver =
        Solver::new(&st, crate::backend::z3_binary::Z3Binary::new("z3").unwrap()).unwrap();
    let x = Int::new_const(&st, "x");
    solver.assert(x.lt(-1)).unwrap();
    let model = solver.check_sat_with_model().unwrap().expect_sat().unwrap();
    match model.eval(x) {
        Some(x) => println!("This is the value of x: {x}"),
        None => panic!("Oh no! This should never happen, as x was part of an assert"),
    }
}

#[test]
fn big_numbers() {
    let st = Storage::new();
    let mut solver =
        Solver::new(&st, crate::backend::z3_binary::Z3Binary::new("z3").unwrap()).unwrap();
    let x = Int::new_const(&st, "x");

    macro_rules! check {
        ($t:ty) => {
            solver
                .scope(|solver| {
                    solver.assert(x._eq(<$t>::MIN)).unwrap();
                    let model = solver.check_sat_with_model().unwrap().expect_sat().unwrap();
                    assert_eq!(<$t>::try_from(model.eval(x).unwrap()), Ok(<$t>::MIN));
                    Ok(())
                })
                .unwrap();
            solver
                .scope(|solver| {
                    solver.assert(x._eq(<$t>::MAX)).unwrap();
                    let model = solver.check_sat_with_model().unwrap().expect_sat().unwrap();
                    assert_eq!(<$t>::try_from(model.eval(x).unwrap()), Ok(<$t>::MAX));
                    Ok(())
                })
                .unwrap();
        };
    }
    check!(i8);
    check!(i16);
    check!(i32);
    check!(i64);
    check!(i128);
    check!(isize);
    check!(u8);
    check!(u16);
    check!(u32);
    check!(u64);
    check!(u128);
    check!(usize);
}

#[test]
fn check_sat_assuming() {
    let st = Storage::new();
    let mut solver =
        Solver::new(&st, crate::backend::z3_binary::Z3Binary::new("z3").unwrap()).unwrap();

    let x = Int::new_const(&st, "x");
    let prop_1 = Bool::new_const(&st, "prop_1");
    let prop_2 = Bool::new_const(&st, "prop_2");
    solver.assert(prop_1.implies(x._eq(42))).unwrap();
    solver.assert(prop_2.implies(x._neq(42))).unwrap();
    solver.assert(*prop_1).unwrap();

    assert_eq!(solver.check_sat().unwrap(), SatResult::Sat);
    assert_eq!(
        solver.check_sat_assuming(&[(prop_2, true)]).unwrap(),
        SatResult::Unsat
    );
    assert_eq!(solver.check_sat().unwrap(), SatResult::Sat);
    assert_eq!(
        solver.check_sat_assuming(&[(prop_2, false)]).unwrap(),
        SatResult::Sat
    );
}

#[test]
fn check_maximize() {
    let st = Storage::new();
    let mut solver =
        Solver::new(&st, crate::backend::z3_binary::Z3Binary::new("z3").unwrap()).unwrap();

    let x = Int::new_const(&st, "x");
    let b = Bool::new_const(&st, "b");
    solver.assert(x.le(100)).unwrap();
    solver.assert(b.implies(x._eq(42))).unwrap();
    solver.maximize(x).unwrap();

    let sat_res = solver.check_sat_with_model().unwrap();
    let model = sat_res.expect_sat().unwrap();
    assert_eq!(model.eval(x).unwrap().to_string(), "100".to_string());
    assert_eq!(model.eval(b).unwrap().to_string(), "false".to_string());
}
