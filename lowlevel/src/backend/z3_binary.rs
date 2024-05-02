use std::ffi::OsStr;

use super::{Backend, BinaryBackend};

pub struct Z3Binary {
    bin: BinaryBackend,
}

impl Z3Binary {
    pub fn new(z3: impl AsRef<OsStr>) -> Result<Self, std::io::Error> {
        Ok(Z3Binary {
            bin: BinaryBackend::new(z3, |cmd| {
                cmd.arg("smtlib2_compliant=true").arg("-in");
            })?,
        })
    }
}

impl Backend for Z3Binary {
    fn exec(&mut self, cmd: &crate::Command) -> Result<String, crate::Error> {
        self.bin.exec(cmd).map(Into::into)
    }
}

#[cfg(feature = "tokio")]
pub mod tokio {
    use std::{ffi::OsStr, future::Future};

    use crate::backend::tokio::TokioBinaryBackend;

    pub struct Z3BinaryTokio {
        bin: TokioBinaryBackend,
    }

    impl Z3BinaryTokio {
        pub async fn new(z3: impl AsRef<OsStr>) -> Result<Self, std::io::Error> {
            Ok(Z3BinaryTokio {
                bin: TokioBinaryBackend::new(z3, |cmd| {
                    cmd.arg("smtlib2_compliant=true").arg("-in");
                })
                .await?,
            })
        }
    }

    impl crate::backend::tokio::TokioBackend for Z3BinaryTokio {
        fn exec(
            &mut self,
            cmd: &crate::Command,
        ) -> impl Future<Output = Result<String, crate::Error>> {
            async move { self.bin.exec(cmd).await.map(Into::into) }
        }
    }
}
