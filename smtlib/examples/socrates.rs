use miette::IntoDiagnostic;
use smtlib::{backend::z3_binary::Z3Binary, funs::Fun, sorts::Sort, Bool, Storage, terms};

fn main() -> miette::Result<()> {
    // Set up miette error handling
    miette::set_panic_hook();

    // Create a new storage for SMT terms
    let st = Storage::new();

    // Create a new solver using Z3
    let mut solver = smtlib::Solver::new(&st, Z3Binary::new("z3").into_diagnostic()?)?;

    // Set the logic to UF (Uninterpreted Functions)
    solver.set_logic(smtlib::Logic::Custom("UF".to_string()))?;

    // Declare a new sort 'S' for entities (humans, etc.)
    let s_sort = Sort::new(&st, "S");
    
    // Create functions with proper sort parameters
    let human = Fun::new(&st, "Human", vec![s_sort.clone()], Bool::sort());
    let mortal = Fun::new(&st, "Mortal", vec![s_sort.clone()], Bool::sort());
    
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
    
    // Create a SortedVar for the quantifier
    // We need to use the SortedVar from lowlevel for the quantifier
    // This is the only part where we need to use the lowlevel API
    let x_var = smtlib_lowlevel::ast::SortedVar(
        smtlib_lowlevel::lexicon::Symbol("x"),
        s_sort.ast()
    );
    let sorted_vars = st.alloc_slice(&[x_var]);
    let all_humans_mortal = smtlib::terms::STerm::new(
        &st,
        smtlib_lowlevel::ast::Term::Forall(sorted_vars, smtlib::terms::STerm::from(human_implies_mortal).into())
    ).into();
    solver.assert(all_humans_mortal)?;

    // Build and assert: Human(Socrates)
    let human_socrates = human.call(&[socrates.into()])?;
    solver.assert(human_socrates.as_bool()?)?;

    // Build and assert: Not(Mortal(Socrates))
    let mortal_socrates = mortal.call(&[socrates.into()])?;
    solver.assert(!mortal_socrates.as_bool()?)?;

    // Check satisfiability
    let result = solver.check_sat()?;
    
    // Print the SMT-LIB representation and result
    println!("SMT-LIB representation of the Socrates syllogism:");
    println!("(set-logic UF)");
    println!("(declare-sort S 0)");
    println!("(declare-fun Human (S) Bool)");
    println!("(declare-fun Mortal (S) Bool)");
    println!("(declare-const Socrates S)");
    println!("(assert (forall ((x S)) (=> (Human x) (Mortal x))))");
    println!("(assert (Human Socrates))");
    println!("(assert (not (Mortal Socrates)))");
    println!("(check-sat)");
    
    println!("\nResult: {}", result);
    println!("\nExplanation:");
    println!("The result should be 'unsat' (unsatisfiable), which proves the syllogism:");
    println!("1. All humans are mortal (forall x, Human(x) => Mortal(x))");
    println!("2. Socrates is human (Human(Socrates))");
    println!("3. Therefore, Socrates is mortal (Mortal(Socrates))");
    println!("By asserting the negation of the conclusion (not Mortal(Socrates))");
    println!("and getting 'unsat', we've proven that the conclusion must be true.");

    Ok(())
}