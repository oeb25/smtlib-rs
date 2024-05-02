use std::ffi::OsStr;

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

#[cfg(feature = "tokio")]
pub mod tokio {
    use std::{ffi::OsStr, future::Future};

    use crate::backend::tokio::TokioBinaryBackend;

    pub struct Cvc5BinaryTokio {
        bin: TokioBinaryBackend,
    }

    impl Cvc5BinaryTokio {
        pub async fn new(cvc5: impl AsRef<OsStr>) -> Result<Self, std::io::Error> {
            Ok(Cvc5BinaryTokio {
                bin: TokioBinaryBackend::new(cvc5, |cmd| {
                    cmd.args(["--lang", "smt2"])
                        .args(["--produce-models"])
                        .args(["--incremental"]);
                })
                .await?,
            })
        }
    }

    impl crate::backend::tokio::TokioBackend for Cvc5BinaryTokio {
        fn exec(
            &mut self,
            cmd: &crate::Command,
        ) -> impl Future<Output = Result<String, crate::Error>> {
            async { self.bin.exec(cmd).await.map(Into::into) }
        }
    }
}
