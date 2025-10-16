use indexmap::{map::Entry, IndexMap, IndexSet};
use itertools::Itertools;
use smtlib_lowlevel::{
    ast::{self, Identifier, QualIdentifier},
    backend,
    lexicon::{Numeral, Symbol},
    Driver, Logger, Storage,
};

use crate::{
    funs, sorts,
    terms::{qual_ident, Const, Dynamic},
    Bool, Error, Logic, Model, SatResult, SatResultWithModel, Sorted,
};

/// The [`Solver`] type is the primary entrypoint to interaction with the
/// solver. Checking for validity of a set of assertions requires:
/// ```
/// # use smtlib::{Int, prelude::*};
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// // 1. Set up storage (TODO: document)
/// let st = smtlib::Storage::new();
/// // 2. Set up the backend (in this case z3)
/// let backend = smtlib::backend::z3_binary::Z3Binary::new("z3")?;
/// // 3. Set up the solver
/// let mut solver = smtlib::Solver::new(&st, backend)?;
/// // 4. Declare the necessary constants
/// let x = Int::new_const(&st, "x");
/// // 5. Add assertions to the solver
/// solver.assert(x._eq(12))?;
/// // 6. Check for validity, and optionally construct a model
/// let sat_res = solver.check_sat_with_model()?;
/// // 7. In this case we expect sat, and thus want to extract the model
/// let model = sat_res.expect_sat()?;
/// // 8. Interpret the result by extract the values of constants which
/// //    satisfy the assertions.
/// match model.eval(x) {
///     Some(x) => println!("This is the value of x: {x}"),
///     None => panic!("Oh no! This should never happen, as x was part of an assert"),
/// }
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct Solver<'st, B> {
    driver: Driver<'st, B>,
    push_pop_stack: Vec<StackSizes>,
    decls: IndexMap<Identifier<'st>, ast::Sort<'st>>,
    declared_sorts: IndexSet<ast::Sort<'st>>,
}

#[derive(Debug)]
struct StackSizes {
    decls: usize,
    declared_sorts: usize,
}

impl<'st, B> Solver<'st, B>
where
    B: backend::Backend,
{
    /// Construct a new solver provided with the backend to use.
    ///
    /// The read more about which backends are available, check out the
    /// documentation of the [`backend`] module.
    pub fn new(st: &'st Storage, backend: B) -> Result<Self, Error> {
        Ok(Self {
            driver: Driver::new(st, backend)?,
            push_pop_stack: Vec::new(),
            decls: Default::default(),
            declared_sorts: Default::default(),
        })
    }
    /// Get the smtlib storage.
    pub fn st(&self) -> &'st Storage {
        self.driver.st()
    }
    /// Set the logger for the solver. This is useful for debugging or tracing
    /// purposes.
    pub fn set_logger(&mut self, logger: impl Logger) {
        self.driver.set_logger(logger)
    }
    /// Set the timeout for the solver. The timeout is in milliseconds.
    pub fn set_timeout(&mut self, ms: usize) -> Result<(), Error> {
        let cmd = ast::Command::SetOption(ast::Option::Attribute(ast::Attribute::WithValue(
            smtlib_lowlevel::lexicon::Keyword(":timeout"),
            ast::AttributeValue::SpecConstant(ast::SpecConstant::Numeral(Numeral::from_usize(ms))),
        )));
        match self.driver.exec(cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e.to_string(), cmd.to_string())),
            ast::GeneralResponse::Unsupported => Err(Error::Unsupported),
            _ => todo!(),
        }
    }
    /// Set the :opt.priority option to the given value
    pub fn set_opt_priority(&mut self, priority: ast::OptimizationPriority) -> Result<(), Error> {
        let cmd = ast::Command::SetOption(ast::Option::OptPriority(priority));

        match self.driver.exec(cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e.to_string(), cmd.to_string())),
            ast::GeneralResponse::Unsupported => Err(Error::Unsupported),
            _ => todo!(),
        }
    }
    /// Explicitly sets the logic for the solver. For some backends this is not
    /// required, as they will infer what ever logic fits the current program.
    ///
    /// To read more about logics read the documentation of [`Logic`].
    pub fn set_logic(&mut self, logic: Logic) -> Result<(), Error> {
        let cmd = ast::Command::SetLogic(Symbol(self.st().alloc_str(&logic.name())));
        match self.driver.exec(cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::SpecificSuccessResponse(_) => todo!(),
            ast::GeneralResponse::Unsupported => todo!(),
            ast::GeneralResponse::Error(_) => todo!(),
        }
    }
    /// Runs the given command on the solver, and returns the result.
    pub fn run_command(
        &mut self,
        cmd: ast::Command<'st>,
    ) -> Result<ast::GeneralResponse<'st>, Error> {
        Ok(self.driver.exec(cmd)?)
    }
    /// Adds the constraint of `b` as an assertion to the solver. To check for
    /// satisfiability call [`Solver::check_sat`] or
    /// [`Solver::check_sat_with_model`].
    pub fn assert(&mut self, b: Bool<'st>) -> Result<(), Error> {
        let term = b.term();

        self.declare_all_consts(term)?;

        let cmd = ast::Command::Assert(term);
        match self.driver.exec(cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e.to_string(), cmd.to_string())),
            _ => todo!(),
        }
    }
    /// Adds the optimization goal of `g` as a goal to the solver.
    pub fn maximize<S>(&mut self, g: S) -> Result<(), Error>
    where
        S: Sorted<'st>,
    {
        let term = g.into().term();

        self.declare_all_consts(term)?;

        let cmd = ast::Command::Maximize(term);

        match self.driver.exec(cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e.to_string(), cmd.to_string())),
            _ => unimplemented!(),
        }
    }
    /// Adds soft-constraint `b` to the solver.
    pub fn assert_soft(&mut self, b: Bool<'st>) -> Result<(), Error> {
        let term = b.term();

        self.declare_all_consts(&term)?;

        let cmd = ast::Command::AssertSoft(term, &[]);

        match self.driver.exec(cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e.to_string(), cmd.to_string())),
            _ => unimplemented!(),
        }
    }
    /// Adds the optimization goal of `g` as a goal to the solver.
    pub fn minimize<S>(&mut self, g: S) -> Result<(), Error>
    where
        S: Sorted<'st>,
    {
        let term = g.into().term();

        self.declare_all_consts(&term)?;

        let cmd = ast::Command::Minimize(term);

        match self.driver.exec(cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e.to_string(), cmd.to_string())),
            _ => unimplemented!(),
        }
    }
    /// Checks for satisfiability of the assertions sent to the solver using
    /// [`Solver::assert`].
    ///
    /// If you are interested in producing a model satisfying the assertions
    /// check out [`Solver::check_sat`].
    pub fn check_sat(&mut self) -> Result<SatResult, Error> {
        let cmd = ast::Command::CheckSat;
        match self.driver.exec(cmd)? {
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
    /// [`Solver::assert`], and produces a [model](Model) in case of `sat`.
    ///
    /// If you are not interested in the produced model, check out
    /// [`Solver::check_sat`].
    pub fn check_sat_with_model(&mut self) -> Result<SatResultWithModel<'st>, Error> {
        match self.check_sat()? {
            SatResult::Unsat => Ok(SatResultWithModel::Unsat),
            SatResult::Sat => Ok(SatResultWithModel::Sat(self.get_model()?)),
            SatResult::Unknown => Ok(SatResultWithModel::Unknown),
        }
    }

    /// Checks for satisfiability of the assertions sent to the solver using
    /// [`Solver::assert`] as well as the ones provided in the assumptions.
    /// A satisfying model can be fetched using [`Solver::get_model`] in case
    /// of `sat`.
    ///
    /// `check_sat_assuming` preserves the context and the given assumptions do
    /// not affect later calls to [`Solver::check_sat`].
    pub fn check_sat_assuming(
        &mut self,
        assumptions: &[(Const<'st, Bool<'st>>, bool)],
    ) -> Result<SatResult, Error> {
        for (assumption, _) in assumptions {
            self.declare_all_consts(assumption.term())?;
        }
        let prop_lits = assumptions
            .iter()
            .map(|(assumption, assume_true)| {
                let symbol = Symbol(assumption.name());
                match assume_true {
                    true => ast::PropLiteral::Symbol(symbol),
                    false => ast::PropLiteral::Not(symbol),
                }
            })
            .collect_vec();
        let prop_lits = self.st().alloc_slice(&prop_lits);
        let cmd = ast::Command::CheckSatAssuming(prop_lits);
        match self.driver.exec(cmd)? {
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
    /// Produces the model for satisfying the assertions. If you are looking to
    /// retrieve a model after calling [`Solver::check_sat`], consider using
    /// [`Solver::check_sat_with_model`] instead.
    ///
    /// > **NOTE:** This must only be called after having called
    /// > [`Solver::check_sat`] and it returning [`SatResult::Sat`].
    pub fn get_model(&mut self) -> Result<Model<'st>, Error> {
        match self.driver.exec(ast::Command::GetModel)? {
            ast::GeneralResponse::SpecificSuccessResponse(
                ast::SpecificSuccessResponse::GetModelResponse(model),
            ) => Ok(Model::new(self.st(), model)),
            res => todo!("{res:?}"),
        }
    }
    /// Declares a function to the solver. For more details refer to the
    /// [`funs`] module.
    pub fn declare_fun(&mut self, fun: &funs::Fun<'st>) -> Result<(), Error> {
        for var in fun.vars {
            self.declare_sort(&var.ast())?;
        }
        self.declare_sort(&fun.return_sort.ast())?;

        if fun.vars.is_empty() {
            return self.declare_const(&qual_ident(fun.name, Some(fun.return_sort.ast())));
        }

        let cmd = ast::Command::DeclareFun(
            Symbol(fun.name),
            self.st()
                .alloc_slice(&fun.vars.iter().map(|s| s.ast()).collect_vec()),
            fun.return_sort.ast(),
        );
        match self.driver.exec(cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e.to_string(), cmd.to_string())),
            _ => todo!(),
        }
    }
    /// Evaluate the given term
    pub fn eval<S>(&mut self, term: S) -> Result<S::Inner, Error>
    where
        S: Sorted<'st>,
        S::Inner: From<&'st ast::Term<'st>>,
    {
        let cmd = ast::Command::Eval(term.into().term());

        match self.driver.exec(cmd)? {
            ast::GeneralResponse::SpecificSuccessResponse(
                ast::SpecificSuccessResponse::EvalResponse(ast::EvalResponse(t)),
            ) => Ok(t.into()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e.to_string(), cmd.to_string())),
            _ => unimplemented!(),
        }
    }
    /// Simplifies the given term
    pub fn simplify(
        &mut self,
        t: Dynamic<'st>,
    ) -> Result<&'st smtlib_lowlevel::ast::Term<'st>, Error> {
        self.declare_all_consts(t.term())?;

        let cmd = ast::Command::Simplify(t.term());

        match self.driver.exec(cmd)? {
            ast::GeneralResponse::SpecificSuccessResponse(
                ast::SpecificSuccessResponse::SimplifyResponse(t),
            ) => Ok(t.0),
            res => todo!("{res:?}"),
        }
    }

    /// Start a new scope, execute the given closure, and then pop the scope.
    ///
    /// A scope is a way to group a set of assertions together, and then later
    /// rollback all the assertions to the state before the scope was started.
    pub fn scope<T>(
        &mut self,
        f: impl FnOnce(&mut Solver<'st, B>) -> Result<T, Error>,
    ) -> Result<T, Error> {
        self.push(1)?;
        let res = f(self)?;
        self.pop(1)?;
        Ok(res)
    }

    fn push(&mut self, levels: usize) -> Result<(), Error> {
        self.push_pop_stack.push(StackSizes {
            decls: self.decls.len(),
            declared_sorts: self.declared_sorts.len(),
        });

        let cmd = ast::Command::Push(Numeral::from_usize(levels));
        match self.driver.exec(cmd)? {
            ast::GeneralResponse::Success => {}
            ast::GeneralResponse::Error(e) => {
                return Err(Error::Smt(e.to_string(), cmd.to_string()));
            }
            _ => todo!(),
        };
        Ok(())
    }

    fn pop(&mut self, levels: usize) -> Result<(), Error> {
        if let Some(sizes) = self.push_pop_stack.pop() {
            self.decls.truncate(sizes.decls);
            self.declared_sorts.truncate(sizes.declared_sorts);
        }

        let cmd = ast::Command::Pop(Numeral::from_usize(levels));
        match self.driver.exec(cmd)? {
            ast::GeneralResponse::Success => {}
            ast::GeneralResponse::Error(e) => {
                return Err(Error::Smt(e.to_string(), cmd.to_string()));
            }
            _ => todo!(),
        };
        Ok(())
    }

    fn declare_all_consts(&mut self, t: &'st ast::Term<'st>) -> Result<(), Error> {
        for q in t.all_consts() {
            self.declare_const(q)?;
        }
        Ok(())
    }

    fn declare_const(&mut self, q: &QualIdentifier<'st>) -> Result<(), Error> {
        match q {
            QualIdentifier::Identifier(_) => {}
            QualIdentifier::Sorted(i, s) => {
                self.declare_sort(s)?;

                match self.decls.entry(*i) {
                    Entry::Occupied(stored) => assert_eq!(s, stored.get()),
                    Entry::Vacant(v) => {
                        v.insert(*s);
                        match i {
                            Identifier::Simple(sym) => {
                                self.driver.exec(ast::Command::DeclareConst(*sym, *s))?;
                            }
                            Identifier::Indexed(_, _) => todo!(),
                        }
                    }
                }
            }
        };
        Ok(())
    }

    fn declare_sort(&mut self, s: &ast::Sort<'st>) -> Result<(), Error> {
        if self.declared_sorts.contains(s) {
            return Ok(());
        }
        self.declared_sorts.insert(*s);

        let cmd = match s {
            ast::Sort::Sort(ident) => {
                let sym = match ident {
                    Identifier::Simple(sym) => sym,
                    Identifier::Indexed(_, _) => {
                        // TODO: is it correct that only sorts from theores can
                        // be indexed, and thus does not need to be declared?
                        return Ok(());
                    }
                };
                if sorts::is_built_in_sort(sym.0) {
                    return Ok(());
                }
                ast::Command::DeclareSort(*sym, Numeral::from_usize(0))
            }
            ast::Sort::Parametric(ident, params) => {
                let sym = match ident {
                    Identifier::Simple(sym) => sym,
                    Identifier::Indexed(_, _) => {
                        // TODO: is it correct that only sorts from theores can
                        // be indexed, and thus does not need to be declared?
                        return Ok(());
                    }
                };
                if sorts::is_built_in_sort(sym.0) {
                    return Ok(());
                }
                ast::Command::DeclareSort(*sym, Numeral::from_usize(params.len()))
            }
        };
        match self.driver.exec(cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e.to_string(), cmd.to_string())),
            _ => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use smtlib_lowlevel::{backend::z3_binary::Z3Binary, Storage};

    use super::Solver;
    use crate::{terms::StaticSorted, Int, SatResult, Sorted};

    #[test]
    fn scope() -> Result<(), crate::Error> {
        let st = Storage::new();
        let mut solver = Solver::new(&st, Z3Binary::new("z3").unwrap())?;

        let x = Int::new_const(&st, "x");

        solver.assert(x._eq(10))?;

        solver.scope(|solver| {
            solver.assert(x._eq(20))?;

            assert_eq!(solver.check_sat()?, SatResult::Unsat);

            Ok(())
        })?;

        assert_eq!(solver.check_sat()?, SatResult::Sat);

        Ok(())
    }
}
