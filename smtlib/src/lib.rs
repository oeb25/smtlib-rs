#![cfg_attr(feature = "const-bit-vec", allow(incomplete_features))]
#![cfg_attr(feature = "const-bit-vec", feature(generic_const_exprs))]
#![doc = include_str!("../README.md")]
#![warn(missing_docs)]

use std::collections::HashMap;

pub use backend::Backend;
use itertools::Itertools;
pub use logics::Logic;
use smtlib_lowlevel::ast;
pub use smtlib_lowlevel::{self as lowlevel, backend, Logger};
pub use terms::Sorted;
use terms::{Const, STerm};

#[cfg(feature = "tokio")]
mod tokio_solver;
#[rustfmt::skip]
#[allow(clippy::all)]
mod logics;
pub mod funs;
mod solver;
pub mod sorts;
pub mod terms;
#[cfg(test)]
mod tests;
pub mod theories;

pub use smtlib_lowlevel::Storage;
pub use solver::Solver;
pub use theories::{core::*, fixed_size_bit_vectors::*, ints::*, reals::*};
#[cfg(feature = "tokio")]
pub use tokio_solver::TokioSolver;

pub mod prelude {
    //! The prelude module contains the most commonly used types and traits in
    //! `smtlib`. It is recommended to import this module when using `smtlib`.

    pub use crate::terms::{Sorted, StaticSorted};
}

/// The satisfiability result produced by a solver
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SatResult {
    /// The solver produced `unsat`
    Unsat,
    /// The solver produced `sat`
    Sat,
    /// The solver produced `unknown`
    Unknown,
}

impl std::fmt::Display for SatResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SatResult::Unsat => write!(f, "unsat"),
            SatResult::Sat => write!(f, "sat"),
            SatResult::Unknown => write!(f, "unknown"),
        }
    }
}

/// The satisfiability result produced by a solver, where the
/// [`Sat`](SatResultWithModel::Sat) variant carries the satisfying model as
/// well.
#[derive(Debug)]
pub enum SatResultWithModel<'st> {
    /// The solver produced `unsat`
    Unsat,
    /// The solver produced `sat` and the associated model
    Sat(Model<'st>),
    /// The solver produced `unknown`
    Unknown,
}

impl<'st> SatResultWithModel<'st> {
    /// Expect the result to be `sat` returning the satisfying model. If not
    /// `sat`, returns an error.
    pub fn expect_sat(self) -> Result<Model<'st>, Error> {
        match self {
            SatResultWithModel::Sat(m) => Ok(m),
            SatResultWithModel::Unsat => Err(Error::UnexpectedSatResult {
                expected: SatResult::Sat,
                actual: SatResult::Unsat,
            }),
            SatResultWithModel::Unknown => Err(Error::UnexpectedSatResult {
                expected: SatResult::Sat,
                actual: SatResult::Unknown,
            }),
        }
    }
}

/// An error that occurred during any stage of using `smtlib`.
#[derive(Debug, thiserror::Error, miette::Diagnostic)]
#[non_exhaustive]
pub enum Error {
    #[error(transparent)]
    #[diagnostic(transparent)]
    /// An error originating from the low-level crate. These can for example be
    /// parsing errors, or solvers occurring with interacting the the solvers.
    Lowlevel(
        #[from]
        #[diagnostic_source]
        smtlib_lowlevel::Error,
    ),
    #[error("SMT error {0} after running {1}")]
    /// An error produced by the SMT solver. These are of the form
    ///
    /// ```ignore
    /// (error "the error goes here")
    /// ```
    Smt(String, String),
    #[error("Expected the model to be {expected} but was {actual}")]
    /// Can occur by calling [`SatResultWithModel::expect_sat`] for example.
    UnexpectedSatResult {
        /// The expected sat result
        expected: SatResult,
        /// The actual sat result
        actual: SatResult,
    },
    /// An error that occurred when trying to cast a dynamic term to a different
    /// sort.
    #[error("tried to cast a dynamic of sort {expected} to {actual}")]
    DynamicCastSortMismatch {
        /// The expected sort
        expected: String,
        /// The actual sort
        actual: String,
    },
}

/// A [`Model`] contains the values of all named constants returned through
/// [`Solver::check_sat_with_model`] or by calling [`Solver::get_model`].
///
/// The two most common usages of [`Model`] is to:
/// - Extract values for constants using [`Model::eval`].
/// - Print out the produced model using `println!("{model}")`.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Model<'st> {
    values: HashMap<String, STerm<'st>>,
}

impl std::fmt::Debug for Model<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.values.fmt(f)
    }
}
impl std::fmt::Display for Model<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{ {} }}",
            self.values
                .iter()
                .sorted_by_key(|(n, _)| n.as_str())
                .map(|(n, t)| format!("{n}: {}", t.term()))
                .format(", ")
        )
    }
}

impl<'st> Model<'st> {
    fn new(st: &'st Storage, model: ast::GetModelResponse<'st>) -> Self {
        Self {
            values: model
                .0
                .iter()
                .map(|res| match res {
                    ast::ModelResponse::DefineFun(f) => (f.0 .0.trim_matches('|').into(), f.3),
                    ast::ModelResponse::DefineFunRec(_) => todo!(),
                    ast::ModelResponse::DefineFunsRec(_, _) => todo!(),
                })
                .map(|(name, term)| (name, STerm::new_from_ref(st, term)))
                .collect(),
        }
    }
    /// Extract the value of a constant. Returns `None` if the value was not
    /// part of the model, which occurs if the constant was not part of any
    /// expression asserted.
    ///
    /// ```
    /// # use smtlib::{Int, Storage, prelude::*};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # let st = Storage::new();
    /// # let mut solver = smtlib::Solver::new(&st, smtlib::backend::z3_binary::Z3Binary::new("z3")?)?;
    /// let x = Int::new_const(&st, "x");
    /// solver.assert(x._eq(12))?;
    /// let model = solver.check_sat_with_model()?.expect_sat()?;
    /// match model.eval(x) {
    ///     Some(x) => println!("This is the value of x: {x}"),
    ///     None => panic!("Oh no! This should never happen, as x was part of an assert"),
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn eval<T: Sorted<'st>>(&self, x: Const<'st, T>) -> Option<T::Inner>
    where
        T::Inner: From<STerm<'st>>,
    {
        Some((*self.values.get(x.name().trim_matches('|'))?).into())
    }
}
