use miette::IntoDiagnostic;
use smtlib::{backend::z3_binary::Z3Binary, funs::Fun, sorts::Sort, terms, Bool, Storage};

fn main() -> miette::Result<()> {
    // Set up miette error handling
    miette::set_panic_hook();

    // Create a new storage for SMT terms
    let st = Storage::new();

    // Create a new solver using Z3
    let mut solver = smtlib::Solver::new(&st, Z3Binary::new("z3").into_diagnostic()?)?;

    // Set a logger to print commands and results
    solver.set_logger((
        |cmd: smtlib_lowlevel::ast::Command<'_>| println!("> {cmd}"),
        |_cmd: smtlib_lowlevel::ast::Command<'_>, res: &str| println!("  => {}", res.trim_end()),
    ));

    // Set the logic to UF (Uninterpreted Functions)
    solver.set_logic(smtlib::Logic::Custom("UF".to_string()))?;

    // Declare a new sort 'S' for entities (humans, etc.)
    let s_sort = Sort::new(&st, "S");

    // Create functions with proper sort parameters
    let human = Fun::new(&st, "Human", vec![s_sort], Bool::sort());
    let mortal = Fun::new(&st, "Mortal", vec![s_sort], Bool::sort());

    // Declare the functions to the solver
    solver.declare_fun(&human)?;
    solver.declare_fun(&mortal)?;

    // Declare a constant 'Socrates' of sort 'S'
    let socrates = s_sort.new_const(&st, "Socrates");

    // Create a variable 'x' of sort 'S' for quantification
    let x = s_sort.new_const(&st, "x");

    // Build the formula: ForAll([x], Implies(Human(x), Mortal(x)))
    let human_x = human.call(&[x.into()])?;
    let mortal_x = mortal.call(&[x.into()])?;
    let human_implies_mortal = human_x.as_bool()?.implies(mortal_x.as_bool()?);

    // Create the universally quantified formula
    let all_humans_mortal = terms::forall(&st, vec![x], human_implies_mortal);
    solver.assert(all_humans_mortal)?;

    // Build and assert: Human(Socrates)
    let human_socrates = human.call(&[socrates.into()])?;
    solver.assert(human_socrates.as_bool()?)?;

    // Build and assert: Not(Mortal(Socrates))
    let mortal_socrates = mortal.call(&[socrates.into()])?;
    let not_mortal_socrates = !mortal_socrates.as_bool()?;
    solver.assert(not_mortal_socrates)?;

    // Check satisfiability
    let result = solver.check_sat()?;

    println!(
        r#"
Result: {result}

Explanation:
The result should be 'unsat' (unsatisfiable), which proves the syllogism:
1. All humans are mortal {all_humans_mortal}
2. Socrates is human {human_socrates}
3. Therefore, Socrates is mortal {mortal_socrates}
By asserting the negation of the conclusion {not_mortal_socrates}
and getting 'unsat', we've proven that the conclusion must be true."#
    );

    Ok(())
}
