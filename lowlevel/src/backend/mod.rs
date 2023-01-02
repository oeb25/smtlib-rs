//! Backends are concrete solvers which can be communicated with using the
//! SMT-LIB language.
//!
//! This module contains the solver which are supported out-of-the-box by
//! `smtlib`. Each backend is feature gated, which means that a feature must be
//! enabled to use the backend.
//!
//! ## Backends
//!
//! - **[`Z3Binary`]**: A [Z3](https://github.com/Z3Prover/z3) backend using the binary CLI interface.
//!     - **Enabled by feature:** `z3`
//! - **[`Cvc5Binary`]**: A [cvc5](https://cvc5.github.io/) backend using the binary CLI interface.
//!     - **Enabled by feature:** `cvc5`

use std::io::{BufRead, Write};

#[cfg(feature = "cvc5")]
mod cvc5;
#[cfg(feature = "cvc5")]
pub use cvc5::*;

#[cfg(feature = "z3")]
mod z3;
#[cfg(feature = "z3")]
pub use z3::*;

/// The [`Backend`] trait is used to interact with SMT solver using the SMT-LIB language.
///
/// For more details read the [`backend`](crate::backend) module documentation.
pub trait Backend: BufRead + Write {}
