use std::{
    ffi::OsStr,
    io::{BufRead, BufReader, Read, Write},
    process::{Child, ChildStdin, ChildStdout},
};

use crate::Backend;

pub struct Z3Binary {
    #[allow(unused)]
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

impl Z3Binary {
    pub fn new(z3: impl AsRef<OsStr>) -> Result<Self, std::io::Error> {
        use std::process::{Command, Stdio};

        let mut child = Command::new(z3.as_ref())
            .arg("smtlib2_compliant=true")
            .arg("-in")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());

        Ok(Z3Binary {
            child,
            stdin,
            stdout,
        })
    }
}

impl Read for Z3Binary {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.stdout.read(buf)
    }
}
impl BufRead for Z3Binary {
    fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
        self.stdout.fill_buf()
    }

    fn consume(&mut self, amt: usize) {
        self.stdout.consume(amt)
    }
}
impl Write for Z3Binary {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.stdin.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.stdin.flush()
    }
}
impl Backend for Z3Binary {}
