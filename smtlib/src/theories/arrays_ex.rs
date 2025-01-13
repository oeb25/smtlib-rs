#![doc = concat!("```ignore\n", include_str!("./ArraysEx.smt2"), "```")]

use std::marker::PhantomData;

use smtlib_lowlevel::ast::Term;

use crate::{
    sorts::Sort,
    terms::{fun, Const, Sorted, Dynamic, StaticSorted},
};

/// Representation of a functional array with extensionality. A possibly
/// unbounded container of values of sort Y, indexed by values of sort X.
#[derive(Debug, Clone)]
pub struct Array<X: Sorted, Y: Sorted>(&'static Term, PhantomData<X>, PhantomData<Y>);

impl<X: Sorted, Y: Sorted> From<Const<Array<X, Y>>> for Array<X, Y> {
    fn from(c: Const<Array<X, Y>>) -> Self {
        c.1
    }
}

impl<X: Sorted, Y: Sorted> std::fmt::Display for Array<X, Y> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<X: StaticSorted, Y: StaticSorted> From<Array<X, Y>> for Dynamic {
    fn from(i: Array<X, Y>) -> Self {
        i.into_dynamic()
    }
}

impl<X: Sorted, Y: Sorted> From<Array<X, Y>> for Term {
    fn from(i: Array<X, Y>) -> Self {
        i.0.clone()
    }
}
impl<X: Sorted, Y: Sorted> From<Term> for Array<X, Y> {
    fn from(t: Term) -> Self {
        Array(Box::leak(Box::new(t)), PhantomData, PhantomData)
    }
}

impl<X: StaticSorted, Y: StaticSorted> StaticSorted for Array<X, Y> {
    type Inner = Self;
    fn static_sort() -> Sort {
        Sort::new_parametric("Array", vec![X::static_sort(), Y::static_sort()])
    }
}

#[allow(unused)]
impl<X: StaticSorted, Y: StaticSorted> Array<X, Y> {
    /// The value stored at `index` --- `(select self index)`
    fn select(&self, index: X) -> Y {
        fun("select", vec![self.0.clone(), index.into()]).into()
    }
    /// Copy of this array with `value` stored at `index` --- `(store self index value)`
    fn store(&self, index: X, value: Y) -> Array<X, Y> {
        fun("store", vec![self.0.clone(), index.into(), value.into()]).into()
    }
}

#[cfg(test)]
mod tests {
    use smtlib_lowlevel::backend::z3_binary::Z3Binary;

    use crate::{terms::{Sorted, StaticSorted}, Int, Solver};

    use super::Array;

    #[test]
    fn define_array() -> Result<(), Box<dyn std::error::Error>> {

        let mut solver = Solver::new(Z3Binary::new("z3")?)?;
        let a = Array::<Int, Int>::new_const("a");

        solver.assert(a.clone()._eq(a.clone()))?;

        let _model = solver.check_sat_with_model()?.expect_sat()?;

        Ok(())
    }

    #[test]
    fn read_stored() -> Result<(), Box<dyn std::error::Error>> {

        let mut solver = Solver::new(Z3Binary::new("z3")?)?;
        let a = Array::<Int, Int>::new_const("a");
        let x = Int::new_const("x");
        let y = Int::new_const("y");

        let updated = a.store(x.into(), y.into());
        let read = updated.select(x.into());

        solver.assert(read._eq(y))?;

        let _model = solver.check_sat_with_model()?.expect_sat()?;

        Ok(())
    }


    #[test]
    fn read_stored_incorrect() -> Result<(), Box<dyn std::error::Error>> {

        let mut solver = Solver::new(Z3Binary::new("z3")?)?;
        let a = Array::<Int, Int>::new_const("a");
        let x = Int::new_const("x");
        let y = Int::new_const("y");

        let updated = a.store(x.into(), y.into());
        let read = updated.select(x.into());

        solver.assert(read._neq(y))?;

        let res = solver.check_sat()?;

        match res {
            crate::SatResult::Unsat => Ok(()),
            s => Err(Box::new(crate::Error::UnexpectedSatResult { expected: crate::SatResult::Unsat, actual: s })),
        }
    }

    #[test]
    fn read_untouched() -> Result<(), Box<dyn std::error::Error>> {

        let mut solver = Solver::new(Z3Binary::new("z3")?)?;
        let a = Array::<Int, Int>::new_const("a");
        let x = Int::new_const("x");
        let y = Int::new_const("y");
        let z = Int::new_const("z");

        let updated = a.store(x.into(), y.into());
        let read = updated.select(z.into());
        
        solver.assert(x._neq(z))?;
        solver.assert(read._neq(y))?;

        let _model = solver.check_sat_with_model()?.expect_sat()?;

        Ok(())
    }

}
