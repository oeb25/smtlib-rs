#![cfg_attr(feature = "const-bit-vec", feature(generic_const_exprs))]
#![doc = include_str!("../README.md")]
#![warn(missing_docs)]

use std::collections::{hash_map::Entry, HashMap};

use itertools::Itertools;
use smtlib_lowlevel::{
    ast::{self, Identifier, QualIdentifier},
    lexicon::Symbol,
    Driver,
};
use terms::Const;
pub use terms::Sort;

pub use backend::Backend;
pub use logics::Logic;
pub use smtlib_lowlevel::backend;

mod logics;
pub mod terms;
pub mod theories;

pub use theories::{core::*, fixed_size_bit_vectors::*, ints::*, reals::*};

/// The satisfiability result produced by a solver
#[derive(Debug)]
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

/// The satisfiability result produced by a solver, where the [`Sat`](SatResultWithModel::Sat) variant
/// carries the satisfying model as well.
#[derive(Debug)]
pub enum SatResultWithModel {
    /// The solver produced `unsat`
    Unsat,
    /// The solver produced `sat` and the associated model
    Sat(Model),
    /// The solver produced `unknown`
    Unknown,
}

impl SatResultWithModel {
    /// Expect the result to be `sat` returning the satisfying model. If not
    /// `sat`, returns an error.
    pub fn expect_sat(self) -> Result<Model, Error> {
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

#[cfg(test)]
mod tests {
    use crate::terms::{forall, Sort};

    use super::*;

    #[test]
    fn int_math() {
        let x = Int::from_name("x");
        let y = Int::from_name("hello");
        // let x_named = x.labeled();
        let mut z = 12 + y * 4;
        z += 3;
        let w = x * x + z;
        println!("{w}");
    }

    #[test]
    fn quantifiers() {
        let x = Int::from_name("x");
        let y = Int::from_name("y");

        let res = forall((x, y), (x + 2)._eq(y));
        println!("{}", ast::Term::from(res));
    }
}

/// The [`Solver`] type is the primary entrypoint to interaction with the
/// solver. Checking for validity of a set of assertions requires:
/// ```
/// # use smtlib::{Int, Sort};
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// // 1. Set up the backend (in this case z3)
/// let backend = smtlib::backend::Z3Binary::new("z3")?;
/// // 2. Set up the solver
/// let mut solver = smtlib::Solver::new(backend)?;
/// // 3. Declare the necessary constants
/// let x = Int::from_name("x");
/// // 4. Add assertions to the solver
/// solver.assert(x._eq(12))?;
/// // 5. Check for validity, and optionally construct a model
/// let sat_res = solver.check_sat_with_model()?;
/// // 6. In this case we expect sat, and thus want to extract the model
/// let model = sat_res.expect_sat()?;
/// // 7. Interpret the result by extract the values of constants which
/// //    satisfy the assertions.
/// match model.eval(x) {
///     Some(x) => println!("This is the value of x: {x}"),
///     None => panic!("Oh no! This should never happen, as x was part of an assert"),
/// }
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct Solver<B> {
    driver: Driver<B>,
    decls: HashMap<Identifier, ast::Sort>,
}

/// An error that occurred during any stage of using `smtlib`.
#[derive(Debug, thiserror::Error, miette::Diagnostic)]
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
}

impl<B> Solver<B>
where
    B: backend::Backend,
{
    /// Construct a new solver provided with the backend to use.
    ///
    /// The read more about which backends are available, check out the
    /// documentation of the [`backend`] module.
    pub fn new(backend: B) -> Result<Self, Error> {
        Ok(Self {
            driver: Driver::new(backend)?,
            decls: Default::default(),
        })
    }
    /// Explicitly sets the logic for the solver. For some backends this is not
    /// required, as they will infer what ever logic fits the current program.
    ///
    /// To read more about logics read the documentation of [`Logic`].
    pub fn set_logic(&mut self, logic: Logic) -> Result<(), Error> {
        let cmd = ast::Command::SetLogic(Symbol(logic.to_string()));
        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::SpecificSuccessResponse(_) => todo!(),
            ast::GeneralResponse::Unsupported => todo!(),
            ast::GeneralResponse::Error(_) => todo!(),
        }
    }
    /// Adds the constraint of `b` as an assertion to the solver. To check for
    /// satisfiability call [`Solver::check_sat`] or
    /// [`Solver::check_sat_with_model`].
    pub fn assert(&mut self, b: Bool) -> Result<(), Error> {
        let term = ast::Term::from(b);
        for q in term.all_consts() {
            match q {
                QualIdentifier::Identifier(_) => {}
                QualIdentifier::Sorted(i, s) => match self.decls.entry(i.clone()) {
                    Entry::Occupied(stored) => assert_eq!(s, stored.get()),
                    Entry::Vacant(v) => {
                        v.insert(s.clone());
                        match i {
                            Identifier::Simple(sym) => {
                                self.driver
                                    .exec(&ast::Command::DeclareConst(sym.clone(), s.clone()))?;
                            }
                            Identifier::Indexed(_, _) => todo!(),
                        }
                    }
                },
            }
        }
        let cmd = ast::Command::Assert(term);
        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e, cmd.to_string())),
            _ => todo!(),
        }
    }
    /// Checks for satisfiability of the assertions sent to the solver using
    /// [`Solver::assert`].
    ///
    /// If you are interested in producing a model satisfying the assertions
    /// check out [`Solver::check_sat`].
    pub fn check_sat(&mut self) -> Result<SatResult, Error> {
        let cmd = ast::Command::CheckSat;
        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::SpecificSuccessResponse(
                ast::SpecificSuccessResponse::CheckSatResponse(res),
            ) => Ok(match res {
                ast::CheckSatResponse::Sat => SatResult::Sat,
                ast::CheckSatResponse::Unsat => SatResult::Unsat,
                ast::CheckSatResponse::Unknown => SatResult::Unknown,
            }),
            ast::GeneralResponse::Error(msg) => Err(Error::Smt(msg, format!("{cmd}"))),
            res => todo!("{res:?}"),
        }
    }
    /// Checks for satisfiability of the assertions sent to the solver using
    /// [`Solver::assert`], and produces a [model](Model) in case of `sat`.
    ///
    /// If you are not interested in the produced model, check out
    /// [`Solver::check_sat`].
    pub fn check_sat_with_model(&mut self) -> Result<SatResultWithModel, Error> {
        match self.check_sat()? {
            SatResult::Unsat => Ok(SatResultWithModel::Unsat),
            SatResult::Sat => Ok(SatResultWithModel::Sat(self.get_model()?)),
            SatResult::Unknown => Ok(SatResultWithModel::Unknown),
        }
    }
    /// Produces the model for satisfying the assertions. If you are looking to
    /// retrieve a model after calling [`Solver::check_sat`], consider using
    /// [`Solver::check_sat_with_model`] instead.
    ///
    /// > **NOTE:** This must only be called after having called
    /// > [`Solver::check_sat`] and it returning [`SatResult::Sat`].
    pub fn get_model(&mut self) -> Result<Model, Error> {
        match self.driver.exec(&ast::Command::GetModel)? {
            ast::GeneralResponse::SpecificSuccessResponse(
                ast::SpecificSuccessResponse::GetModelResponse(model),
            ) => Ok(Model::new(model)),
            res => todo!("{res:?}"),
        }
    }
}

/// A [`Model`] contains the values of all named constants returned through
/// [`Solver::check_sat_with_model`] or by calling [`Solver::get_model`].
///
/// The two most common usages of [`Model`] is to:
/// - Extract values for constants using [`Model::eval`].
/// - Print out the produced model using `println!("{model}")`.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Model {
    values: HashMap<String, ast::Term>,
}

impl std::fmt::Debug for Model {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.values.fmt(f)
    }
}
impl std::fmt::Display for Model {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{ {} }}",
            self.values
                .iter()
                .map(|(n, t)| format!("{n}: {t}"))
                .format(", ")
        )
    }
}

impl Model {
    fn new(model: ast::GetModelResponse) -> Self {
        Self {
            values: model
                .0
                .into_iter()
                .map(|res| match res {
                    ast::ModelResponse::DefineFun(f) => (f.0 .0.trim_matches('|').into(), f.3),
                    ast::ModelResponse::DefineFunRec(_) => todo!(),
                    ast::ModelResponse::DefineFunsRec(_, _) => todo!(),
                })
                .collect(),
        }
    }
    /// Extract the value of a constant. Returns `None` if the value was not
    /// part of the model, which occurs if the constant was not part of any
    /// expression asserted.
    ///
    /// ```
    /// # use smtlib::{Int, Sort};
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # let mut solver = smtlib::Solver::new(smtlib::backend::Z3Binary::new("z3")?)?;
    /// let x = Int::from_name("x");
    /// solver.assert(x._eq(12))?;
    /// let model = solver.check_sat_with_model()?.expect_sat()?;
    /// match model.eval(x) {
    ///     Some(x) => println!("This is the value of x: {x}"),
    ///     None => panic!("Oh no! This should never happen, as x was part of an assert"),
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn eval<T: Sort>(&self, x: Const<T>) -> Option<T::Inner>
    where
        T::Inner: From<ast::Term>,
    {
        Some(self.values.get(x.name().trim_matches('|'))?.clone().into())
    }
}
