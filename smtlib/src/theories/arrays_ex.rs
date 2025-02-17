#![doc = concat!("```ignore\n", include_str!("./ArraysEx.smt2"), "```")]

use std::marker::PhantomData;

use smtlib_lowlevel::ast;

use crate::terms::{app, Const, IntoWithStorage, STerm, Sorted, StaticSorted};

/// Representation of a functional array with extensionality. A possibly
/// unbounded container of values of sort Y, indexed by values of sort X.
#[derive(Debug)]
pub struct Array<'st, X: Sorted<'st>, Y: Sorted<'st>>(STerm<'st>, PhantomData<X>, PhantomData<Y>);

impl<'st, X: Sorted<'st>, Y: Sorted<'st>> Clone for Array<'st, X, Y> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'st, X: Sorted<'st>, Y: Sorted<'st>> Copy for Array<'st, X, Y> {}

impl<'st, X: Sorted<'st>, Y: Sorted<'st>> IntoWithStorage<'st, Array<'st, X, Y>>
    for Const<'st, Array<'st, X, Y>>
{
    fn into_with_storage(self, _st: &'st smtlib_lowlevel::Storage) -> Array<'st, X, Y> {
        self.1
    }
}

impl<'st, X: StaticSorted<'st>, Y: StaticSorted<'st>> From<STerm<'st>> for Array<'st, X, Y> {
    fn from(t: STerm<'st>) -> Self {
        Array(t, PhantomData, PhantomData)
    }
}
impl<'st, X: StaticSorted<'st>, Y: StaticSorted<'st>> From<Array<'st, X, Y>> for STerm<'st> {
    fn from(value: Array<'st, X, Y>) -> Self {
        value.0
    }
}

impl<'st, X: StaticSorted<'st>, Y: StaticSorted<'st>> StaticSorted<'st> for Array<'st, X, Y> {
    type Inner = Self;

    const AST_SORT: ast::Sort<'static> =
        ast::Sort::new_simple_parametric("Array", &[X::AST_SORT, Y::AST_SORT]);

    fn static_st(&self) -> &'st smtlib_lowlevel::Storage {
        self.0.st()
    }
}

#[allow(unused)]
impl<'st, X: StaticSorted<'st>, Y: StaticSorted<'st>> Array<'st, X, Y> {
    /// The value stored at `index` --- `(select self index)`
    fn select(self, index: X) -> Y {
        app(self.st(), "select", (self.0.term(), index.term())).into()
    }
    /// Copy of this array with `value` stored at `index` --- `(store self index
    /// value)`
    fn store(self, index: X, value: Y) -> Array<'st, X, Y> {
        app(
            self.st(),
            "store",
            (self.0.term(), index.term(), value.term()),
        )
        .into()
    }
}

#[cfg(test)]
mod tests {
    use smtlib_lowlevel::backend::z3_binary::Z3Binary;

    use super::Array;
    use crate::{
        terms::{Sorted, StaticSorted},
        Int, Solver, Storage,
    };

    /// Check that an array can be defined using the high-level API
    #[test]
    fn define_array() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut solver = Solver::new(&st, Z3Binary::new("z3")?)?;
        let a = Array::<Int, Int>::new_const(&st, "a");

        solver.assert(a._eq(a))?;

        let _model = solver.check_sat_with_model()?.expect_sat()?;

        Ok(())
    }

    /// Check that a value stored at an index can be correctly retrieved
    #[test]
    fn read_stored() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut solver = Solver::new(&st, Z3Binary::new("z3")?)?;
        let a = Array::<Int, Int>::new_const(&st, "a");
        let x = Int::new_const(&st, "x");
        let y = Int::new_const(&st, "y");

        let updated = a.store(x.into(), y.into());
        let read = updated.select(x.into());

        solver.assert(read._eq(y))?;

        let _model = solver.check_sat_with_model()?.expect_sat()?;

        Ok(())
    }

    /// Check that a value stored at an index is guaranteed to be retrieved
    #[test]
    fn read_stored_incorrect() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut solver = Solver::new(&st, Z3Binary::new("z3")?)?;
        let a = Array::<Int, Int>::new_const(&st, "a");
        let x = Int::new_const(&st, "x");
        let y = Int::new_const(&st, "y");

        let updated = a.store(x.into(), y.into());
        let read = updated.select(x.into());

        solver.assert(read._neq(y))?;

        let res = solver.check_sat()?;

        match res {
            crate::SatResult::Unsat => Ok(()),
            s => Err(Box::new(crate::Error::UnexpectedSatResult {
                expected: crate::SatResult::Unsat,
                actual: s,
            })),
        }
    }

    /// Check that a store does not affect values other than the target index
    #[test]
    fn read_untouched() -> Result<(), Box<dyn std::error::Error>> {
        let st = Storage::new();
        let mut solver = Solver::new(&st, Z3Binary::new("z3")?)?;
        let a = Array::<Int, Int>::new_const(&st, "a");
        let x = Int::new_const(&st, "x");
        let y = Int::new_const(&st, "y");
        let z = Int::new_const(&st, "z");

        let updated = a.store(x.into(), y.into());
        let read = updated.select(z.into());

        solver.assert(x._neq(z))?;
        solver.assert(read._neq(y))?;

        let _model = solver.check_sat_with_model()?.expect_sat()?;

        Ok(())
    }
}
