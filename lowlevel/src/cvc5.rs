use std::{
    ffi::OsStr,
    io::{BufRead, BufReader, Read, Write},
    process::{Child, ChildStdin, ChildStdout},
};

use crate::Backend;

pub struct Cvc5Binary {
    #[allow(unused)]
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

impl Cvc5Binary {
    pub fn new(cvc5: impl AsRef<OsStr>) -> Result<Self, std::io::Error> {
        use std::process::{Command, Stdio};

        let mut child = Command::new(cvc5.as_ref())
            .args(&["--lang", "smt2"])
            .args(&["--produce-models"])
            .args(&["--incremental"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());

        Ok(Cvc5Binary {
            child,
            stdin,
            stdout,
        })
    }
}

impl Read for Cvc5Binary {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.stdout.read(buf)
    }
}
impl BufRead for Cvc5Binary {
    fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
        self.stdout.fill_buf()
    }

    fn consume(&mut self, amt: usize) {
        self.stdout.consume(amt)
    }
}
impl Write for Cvc5Binary {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.stdin.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.stdin.flush()
    }
}
impl Backend for Cvc5Binary {}
