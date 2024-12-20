use indexmap::{IndexMap, IndexSet, map::Entry};
use smtlib_lowlevel::{
    Driver, Logger,
    ast::{
        self, EvalResponse, GeneralResponse, Identifier, OptimizationPriority, QualIdentifier,
        SpecificSuccessResponse, Term,
    },
    backend,
    lexicon::{Numeral, Symbol},
};

use crate::{
    Bool, Error, Logic, Model, SatResult, SatResultWithModel, Sorted, funs, sorts,
    terms::{Dynamic, qual_ident},
};

/// The [`Solver`] type is the primary entrypoint to interaction with the
/// solver. Checking for validity of a set of assertions requires:
/// ```
/// # use smtlib::{Int, prelude::*};
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// // 1. Set up the backend (in this case z3)
/// let backend = smtlib::backend::z3_binary::Z3Binary::new("z3")?;
/// // 2. Set up the solver
/// let mut solver = smtlib::Solver::new(backend)?;
/// // 3. Declare the necessary constants
/// let x = Int::new_const("x");
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
    push_pop_stack: Vec<StackSizes>,
    decls: IndexMap<Identifier, ast::Sort>,
    declared_sorts: IndexSet<ast::Sort>,
}

#[derive(Debug)]
struct StackSizes {
    decls: usize,
    declared_sorts: usize,
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
            push_pop_stack: Vec::new(),
            decls: Default::default(),
            declared_sorts: Default::default(),
        })
    }

    pub fn set_logger(&mut self, logger: impl Logger) {
        self.driver.set_logger(logger)
    }

    pub fn set_timeout(&mut self, ms: usize) -> Result<(), Error> {
        let cmd = ast::Command::SetOption(ast::Option::Attribute(ast::Attribute::WithValue(
            smtlib_lowlevel::lexicon::Keyword(":timeout".to_string()),
            ast::AttributeValue::SpecConstant(ast::SpecConstant::Numeral(Numeral(ms.to_string()))),
        )));
        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e, cmd.to_string())),
            _ => todo!(),
        }
    }

    /// sets the :opt.priority option to the given value
    pub fn set_opt_priority(&mut self, priority: ast::OptimizationPriority) -> Result<(), Error> {
        let cmd = ast::Command::SetOption(ast::Option::OptPriority(priority));

        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e, cmd.to_string())),
            _ => unimplemented!(),
        }
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

    /// Runs the given command on the solver, and returns the result.
    pub fn run_command(&mut self, cmd: &ast::Command) -> Result<ast::GeneralResponse, Error> {
        Ok(self.driver.exec(cmd)?)
    }

    /// Adds the constraint of `b` as an assertion to the solver. To check for
    /// satisfiability call [`Solver::check_sat`] or
    /// [`Solver::check_sat_with_model`].
    pub fn assert(&mut self, b: Bool) -> Result<(), Error> {
        let term = b.into();

        self.declare_all_consts(&term)?;

        let cmd = ast::Command::Assert(term);
        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e, cmd.to_string())),
            _ => todo!(),
        }
    }

    /// Adds the optimization goal of `g` as a goal to the solver.
    pub fn maximize<S>(&mut self, g: S) -> Result<(), Error>
    where
        S: Sorted,
    {
        let term = g.into();

        self.declare_all_consts(&term)?;

        let cmd = ast::Command::Maximize(term);

        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e, cmd.to_string())),
            _ => unimplemented!(),
        }
    }

    /// Adds soft-constraint `b` to the solver.
    pub fn assert_soft(&mut self, b: Bool) -> Result<(), Error> {
        let term = b.into();

        self.declare_all_consts(&term)?;

        let cmd = ast::Command::AssertSoft(term, vec![]);

        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e, cmd.to_string())),
            _ => unimplemented!(),
        }
    }

    /// Adds the optimization goal of `g` as a goal to the solver.
    pub fn minimize<S>(&mut self, g: S) -> Result<(), Error>
    where
        S: Sorted,
    {
        let term = g.into();

        self.declare_all_consts(&term)?;

        let cmd = ast::Command::Minimize(term);

        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e, cmd.to_string())),
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
        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::SpecificSuccessResponse(
                ast::SpecificSuccessResponse::CheckSatResponse(res),
            ) => {
                Ok(match res {
                    ast::CheckSatResponse::Sat => SatResult::Sat,
                    ast::CheckSatResponse::Unsat => SatResult::Unsat,
                    ast::CheckSatResponse::Unknown => SatResult::Unknown,
                })
            }
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

    pub fn declare_fun(&mut self, fun: &funs::Fun) -> Result<(), Error> {
        for var in &fun.vars {
            self.declare_sort(&var.ast())?;
        }
        self.declare_sort(&fun.return_sort.ast())?;

        if fun.vars.is_empty() {
            return self.declare_const(&qual_ident(fun.name.clone(), Some(fun.return_sort.ast())));
        }

        let cmd = ast::Command::DeclareFun(
            Symbol(fun.name.clone()),
            fun.vars.iter().map(|s| s.ast()).collect(),
            fun.return_sort.ast(),
        );
        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => Err(Error::Smt(e, cmd.to_string())),
            _ => todo!(),
        }
    }

    /// Simplifies the given term
    pub fn simplify(&mut self, t: Dynamic) -> Result<smtlib_lowlevel::ast::Term, Error> {
        self.declare_all_consts(&t.into())?;

        let cmd = ast::Command::Simplify(t.into());

        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::SpecificSuccessResponse(
                ast::SpecificSuccessResponse::SimplifyResponse(t),
            ) => Ok(t.0),
            res => todo!("{res:?}"),
        }
    }

    pub fn eval<S>(&mut self, term: S) -> Result<S::Inner, Error>
    where
        S: Sorted,
        S::Inner: From<Term>,
    {
        let cmd = ast::Command::Eval(term.into());

        match self.driver.exec(&cmd)? {
            GeneralResponse::SpecificSuccessResponse(SpecificSuccessResponse::EvalResponse(
                EvalResponse(t),
            )) => Ok(t.into()),
            GeneralResponse::Error(e) => Err(Error::Smt(e, cmd.to_string())),
            _ => unimplemented!(),
        }
    }

    pub fn scope<T>(
        &mut self,
        f: impl FnOnce(&mut Solver<B>) -> Result<T, Error>,
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

        let cmd = ast::Command::Push(Numeral(levels.to_string()));
        Ok(match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => {}
            ast::GeneralResponse::Error(e) => return Err(Error::Smt(e, cmd.to_string())),
            _ => todo!(),
        })
    }

    fn pop(&mut self, levels: usize) -> Result<(), Error> {
        if let Some(sizes) = self.push_pop_stack.pop() {
            self.decls.truncate(sizes.decls);
            self.declared_sorts.truncate(sizes.declared_sorts);
        }

        let cmd = ast::Command::Pop(Numeral(levels.to_string()));
        Ok(match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => {}
            ast::GeneralResponse::Error(e) => return Err(Error::Smt(e, cmd.to_string())),
            _ => todo!(),
        })
    }

    fn declare_all_consts(&mut self, t: &ast::Term) -> Result<(), Error> {
        for q in t.all_consts() {
            self.declare_const(q)?;
        }
        Ok(())
    }

    fn declare_const(&mut self, q: &QualIdentifier) -> Result<(), Error> {
        Ok(match q {
            QualIdentifier::Identifier(_) => {}
            QualIdentifier::Sorted(i, s) => {
                self.declare_sort(s)?;

                match self.decls.entry(i.clone()) {
                    Entry::Occupied(stored) => assert_eq!(s, stored.get()),
                    Entry::Vacant(v) => {
                        v.insert(s.clone());
                        match i {
                            Identifier::Simple(sym) => {
                                self.driver
                                    .exec(&ast::Command::DeclareConst(sym.clone(), s.clone()))?;
                            }
                            Identifier::Indexed(..) => todo!(),
                        }
                    }
                }
            }
        })
    }

    fn declare_sort(&mut self, s: &ast::Sort) -> Result<(), Error> {
        if self.declared_sorts.contains(s) {
            return Ok(());
        }
        self.declared_sorts.insert(s.clone());

        let cmd = match s {
            ast::Sort::Sort(ident) => {
                let sym = match ident {
                    Identifier::Simple(sym) => sym,
                    Identifier::Indexed(..) => {
                        // TODO: is it correct that only sorts from theores can
                        // be indexed, and thus does not need to be declared?
                        return Ok(());
                    }
                };
                if sorts::is_built_in_sort(&sym.0) {
                    return Ok(());
                }
                ast::Command::DeclareSort(sym.clone(), Numeral("0".to_string()))
            }
            ast::Sort::Parametric(ident, params) => {
                let sym = match ident {
                    Identifier::Simple(sym) => sym,
                    Identifier::Indexed(..) => {
                        // TODO: is it correct that only sorts from theores can
                        // be indexed, and thus does not need to be declared?
                        return Ok(());
                    }
                };
                if sorts::is_built_in_sort(&sym.0) {
                    return Ok(());
                }
                ast::Command::DeclareSort(sym.clone(), Numeral(params.len().to_string()))
            }
        };
        match self.driver.exec(&cmd)? {
            ast::GeneralResponse::Success => Ok(()),
            ast::GeneralResponse::Error(e) => return Err(Error::Smt(e, cmd.to_string())),
            _ => todo!(),
        }
    }
}
