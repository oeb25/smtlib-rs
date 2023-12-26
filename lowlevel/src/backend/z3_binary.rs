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

#[cfg(feature = "async")]
#[async_trait::async_trait(?Send)]
impl super::AsyncBackend for Z3Binary {
    async fn exec(&mut self, cmd: &crate::Command) -> Result<String, crate::Error> {
        self.bin.exec(cmd).map(Into::into)
    }
}
