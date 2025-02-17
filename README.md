# smtlib

[![Crates.io](https://img.shields.io/crates/v/smtlib.svg)](https://crates.io/crates/smtlib)
[![Docs](https://docs.rs/smtlib/badge.svg)](https://docs.rs/smtlib)
[![Crates.io license shield](https://img.shields.io/crates/l/smtlib.svg)](https://crates.io/crates/smtlib)

> A high-level API for interacting with SMT solvers

_If you are looking for more control and less ergonomics, take a look at the [low-level crate `smtlib-lowlevel`](https://crates.io/crates/smtlib-lowlevel) for construct SMT-LIB code and talking directly with SMT solvers._

## Background

[Satisfiability modulo theories (SMT)](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories) is the problem of determining whether or not a mathematical formula is satisfiable. SMT solvers (such as [Z3](https://github.com/Z3Prover/z3) and [cvc5](https://cvc5.github.io/)) are programs to automate this process. These are fantastic tools which are very powerful and can solve complex problems efficiently.

To communicate with the solvers, the [SMT-LIB](https://smtlib.cs.uiowa.edu/index.shtml) specification has been made to standardize the input/output language to all of the solvers.

Writing this format by-hand (or "programmatically by-hand") can at times be tedious and error prone. Even more so is interpreting the result produced by the solvers.

Thus the goal of `smtlib` (and [`smtlib-lowlevel`](https://crates.io/crates/smtlib-lowlevel)) is to provide ergonomic API's for communicating with the solvers, independent of the concrete solver.

## Usage

The primary way to use `smtlib` is by constructing a [`smtlib::Solver`](https://docs.rs/smtlib/latest/smtlib/struct.Solver.html). A solver takes as argument a [`smtlib::Backend`](https://docs.rs/smtlib/latest/smtlib/trait.Backend.html). To see which backends are provided with the library check out the [`smtlib::backend`](https://docs.rs/smtlib/latest/smtlib/backend/index.html) module. Some backend is behind a feature flag, so for example to use the [Z3](https://github.com/Z3Prover/z3) statically backend install `smtlib` by running `cargo add smtlib -F z3-static`, but otherwise add it by running:

```bash
cargo add smtlib
```

Now you can go ahead and use the library in your project.

```rust
use smtlib::{backend::z3_binary::Z3Binary, Int, SatResultWithModel, Solver, Storage, prelude::*};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let st = Storage::new();

    // Initialize the solver with the Z3 backend. The "z3" string refers the
    // to location of the already installed `z3` binary. In this case, the
    // binary is in the path.
    let mut solver = Solver::new(&st, Z3Binary::new("z3")?)?;

    // Declare two new variables
    let x = Int::new_const(&st, "x");
    let y = Int::new_const(&st, "y");

    // Assert some constraints. This tells the solver that these expressions
    // must be true, so any solution will satisfy these.
    solver.assert(x._eq(y + 25))?;
    solver.assert(x._eq(204))?;
    // The constraints are thus:
    // - x == y + 25
    // - x == 204
    // Note that we use `a._eq(b)` rather than `a == b`, since we want to
    // express the mathematical relation of `a` and `b`, while `a == b` checks
    // that the two **expressions** are structurally the same.

    // Check for validity
    match solver.check_sat_with_model()? {
        SatResultWithModel::Sat(model) => {
            // Since it is valid, we can extract the possible values of the
            // variables using a model
            println!("x = {}", model.eval(x).unwrap());
            println!("y = {}", model.eval(y).unwrap());
        }
        SatResultWithModel::Unsat => println!("No valid solutions found!"),
        SatResultWithModel::Unknown => println!("Satisfaction remains unknown..."),
    }

    Ok(())
}
```
