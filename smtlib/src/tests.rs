use terms::StaticSorted;

use super::*;
use crate::terms::{Sorted, forall};

#[test]
fn int_math() {
    let x = Int::new_const("x");
    let y = Int::new_const("hello");
    // let x_named = x.labeled();
    let mut z = 12 + y * 4;
    z += 3;
    let w = x * x + z;
    println!("{w}");
}

#[test]
fn quantifiers() {
    let x = Int::new_const("x");
    let y = Int::new_const("y");

    let res = forall((x, y), (x + 2)._eq(y));
    println!("{}", ast::Term::from(res));
}

#[test]
fn negative_numbers() {
    let mut solver = Solver::new(crate::backend::z3_binary::Z3Binary::new("z3").unwrap()).unwrap();
    let x = Int::new_const("x");
    solver.assert(x.lt(-1)).unwrap();
    let model = solver.check_sat_with_model().unwrap().expect_sat().unwrap();
    match model.eval(x) {
        Some(x) => println!("This is the value of x: {x}"),
        None => panic!("Oh no! This should never happen, as x was part of an assert"),
    }
}
