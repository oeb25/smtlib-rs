use std::collections::{hash_map::Entry, HashMap};

use smtlib_lowlevel::{
    ast::{self, Identifier, QualIdentifier},
    backend,
    lexicon::Symbol,
    tokio::TokioDriver,
    Storage,
};

use crate::{Bool, Error, Logic, Model, SatResult, SatResultWithModel, Sorted};

/// The [`TokioSolver`] type is the primary entrypoint to interaction with the
/// solver. Checking for validity of a set of assertions requires:
/// ```
/// # use smtlib::{Int, prelude::*};
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// # tokio_test::block_on(async {
/// // 1. Set up storage (TODO: document)
/// let st = smtlib::Storage::new();
/// // 2. Set up the backend (in this case z3)
/// let backend = smtlib::backend::z3_binary::tokio::Z3BinaryTokio::new("z3").await?;
/// // 3. Set up the solver
/// let mut solver = smtlib::TokioSolver::new(&st, backend).await?;
/// // 4. Declare the necessary constants
/// let x = Int::new_const(&st, "x");
/// // 5. Add assertions to the solver
/// solver.assert(x._eq(12)).await?;
/// // 6. Check for validity, and optionally construct a model
/// let sat_res = solver.check_sat_with_model().await?;
/// // 7. In this case we expect sat, and thus want to extract the model
/// let model = sat_res.expect_sat()?;
/// // 8. Interpret the result by extract the values of constants which
/// //    satisfy the assertions.
/// match model.eval(x) {
///     Some(x) => println!("This is the value of x: {x}"),
///     None => panic!("Oh no! This should never happen, as x was part of an assert"),
/// }
/// # Ok(())
/// # })
/// # }
/// ```
#[derive(Debug)]
pub struct TokioSolver<'st, B> {
    driver: TokioDriver<'st, B>,
    decls: HashMap<Identifier<'st>, ast::Sort<'st>>,
}

impl<'st, B> TokioSolver<'st, B>
where
    B: backend::tokio::TokioBackend,
{
    /// Construct a new solver provided with the backend to use.
    ///
    /// The read more about which backends are available, check out the
    /// documentation of the [`backend`] module.
    pub async fn new(st: &'st Storage, backend: B) -> Result<Self, Error> {
        Ok(Self {
            driver: TokioDriver::new(st, backend).await?,
            decls: Default::default(),
        })
    }
    /// Returns the storage used by the solver.
    pub fn st(&self) -> &'st Storage {
        self.driver.st()
    }
    /// Explicitly sets the logic for the solver. For some backends this is not
    /// required, as they will infer what ever logic fits the current program.
    ///
    /// To read more about logics read the documentation of [`Logic`].
    pub async fn set_logic(&mut self, logic: Logic) -> Result<(), Error> {
        let cmd = ast::Command::SetLogic(Symbol(self.st().alloc_str(&logic.name())));
        match self.driver.exec(cmd).await? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::SpecificSuccessResponse(_) => todo!(),
            ast::GeneralResponse::Unsupported => todo!(),
            ast::GeneralResponse::Error(_) => todo!(),
        }
    }
    /// Runs the given command on the solver, and returns the result.
    pub async fn run_command(
        &mut self,
        cmd: ast::Command<'st>,
    ) -> Result<ast::GeneralResponse<'st>, Error> {
        Ok(self.driver.exec(cmd).await?)
    }
    /// Adds the constraint of `b` as an assertion to the solver. To check for
    /// satisfiability call [`TokioSolver::check_sat`] or
    /// [`TokioSolver::check_sat_with_model`].
    pub async fn assert(&mut self, b: Bool<'st>) -> Result<(), Error> {
        let term = b.term();
        for q in term.all_consts() {
            match q {
                QualIdentifier::Identifier(_) => {}
                QualIdentifier::Sorted(i, s) => match self.decls.entry(*i) {
                    Entry::Occupied(stored) => assert_eq!(s, stored.get()),
                    Entry::Vacant(v) => {
                        v.insert(*s);
                        match i {
                            Identifier::Simple(sym) => {
                                self.driver
                                    .exec(ast::Command::DeclareConst(*sym, *s))
                                    .await?;
                            }
                            Identifier::Indexed(_, _) => todo!(),
                        }
                    }
                },
            }
        }
        let cmd = ast::Command::Assert(term);
        match self.driver.exec(cmd).await? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e.to_string(), cmd.to_string())),
            _ => todo!(),
        }
    }
    /// Checks for satisfiability of the assertions sent to the solver using
    /// [`TokioSolver::assert`].
    ///
    /// If you are interested in producing a model satisfying the assertions
    /// check out [`TokioSolver::check_sat`].
    pub async fn check_sat(&mut self) -> Result<SatResult, Error> {
        let cmd = ast::Command::CheckSat;
        match self.driver.exec(cmd).await? {
            ast::GeneralResponse::SpecificSuccessResponse(
                ast::SpecificSuccessResponse::CheckSatResponse(res),
            ) => Ok(match res {
                ast::CheckSatResponse::Sat => SatResult::Sat,
                ast::CheckSatResponse::Unsat => SatResult::Unsat,
                ast::CheckSatResponse::Unknown => SatResult::Unknown,
            }),
            ast::GeneralResponse::Error(msg) => Err(Error::Smt(msg.to_string(), format!("{cmd}"))),
            res => todo!("{res:?}"),
        }
    }
    /// Checks for satisfiability of the assertions sent to the solver using
    /// [`TokioSolver::assert`], and produces a [model](Model) in case of `sat`.
    ///
    /// If you are not interested in the produced model, check out
    /// [`TokioSolver::check_sat`].
    pub async fn check_sat_with_model(&mut self) -> Result<SatResultWithModel, Error> {
        match self.check_sat().await? {
            SatResult::Unsat => Ok(SatResultWithModel::Unsat),
            SatResult::Sat => Ok(SatResultWithModel::Sat(self.get_model().await?)),
            SatResult::Unknown => Ok(SatResultWithModel::Unknown),
        }
    }
    /// Produces the model for satisfying the assertions. If you are looking to
    /// retrieve a model after calling [`TokioSolver::check_sat`], consider
    /// using [`TokioSolver::check_sat_with_model`] instead.
    ///
    /// > **NOTE:** This must only be called after having called
    /// > [`TokioSolver::check_sat`] and it returning [`SatResult::Sat`].
    pub async fn get_model(&mut self) -> Result<Model, Error> {
        match self.driver.exec(ast::Command::GetModel).await? {
            ast::GeneralResponse::SpecificSuccessResponse(
                ast::SpecificSuccessResponse::GetModelResponse(model),
            ) => Ok(Model::new(self.st(), model)),
            res => todo!("{res:?}"),
        }
    }
}

#[cfg(test)]
mod tests {

    use smtlib_lowlevel::backend::z3_binary::tokio::Z3BinaryTokio;

    use super::TokioSolver;
    use crate::{terms::StaticSorted, Int, Sorted};

    type Result<T, E = crate::Error> = std::result::Result<T, E>;

    #[tokio::test]
    async fn basic() -> Result<(), Box<dyn std::error::Error>> {
        let st = smtlib_lowlevel::Storage::new();

        let mut solver = TokioSolver::new(&st, Z3BinaryTokio::new("z3").await?).await?;

        let x = Int::new_const(&st, "x");
        let y = Int::new_const(&st, "y");

        solver.assert(x._eq(10)).await?;
        solver.assert(y._eq(x + 2)).await?;

        let model = solver.check_sat_with_model().await?.expect_sat()?;

        insta::assert_display_snapshot!(model, @"{ x: 10, y: 12 }");

        Ok(())
    }
}
