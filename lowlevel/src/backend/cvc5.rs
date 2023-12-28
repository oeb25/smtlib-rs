use std::{ffi::OsStr, future::Future};

use super::{Backend, BinaryBackend};

pub struct Cvc5Binary {
    bin: BinaryBackend,
}

impl Cvc5Binary {
    pub fn new(cvc5: impl AsRef<OsStr>) -> Result<Self, std::io::Error> {
        Ok(Cvc5Binary {
            bin: BinaryBackend::new(cvc5, |cmd| {
                cmd.args(["--lang", "smt2"])
                    .args(["--produce-models"])
                    .args(["--incremental"]);
            })?,
        })
    }
}

impl Backend for Cvc5Binary {
    fn exec(&mut self, cmd: &crate::Command) -> Result<String, crate::Error> {
        self.bin.exec(cmd).map(Into::into)
    }
}

impl super::AsyncBackend for Cvc5Binary {
    fn exec_async(
        &mut self,
        cmd: &crate::Command,
    ) -> impl Future<Output = Result<String, crate::Error>> {
        async { self.bin.exec(cmd).map(Into::into) }
    }
}
