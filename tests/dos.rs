use std::convert::Into;
use std::error::Error;
use std::fs;
use std::process::{Command, Output};
use std::result;

type Result<T> = result::Result<T, Box<dyn Error>>;

fn cmd(name: &str) -> Result<Output> {
    Command::new("./target/debug/bandera")
        .arg(format!("./tests/asm/dos/{}", name))
        .output()
        .map_err(Into::into)
}

fn read_file(name: &str) -> Result<String> {
    let path = format!("./tests/output/dos/{}", name);
    fs::read_to_string(path).map_err(Into::into)
}

#[test]
fn exit() -> Result<()> {
    let output = cmd("exit.asm")?;

    assert_eq!(output.status.code(), Some(42 as i32));
    Ok(())
}

#[test]
fn hello() -> Result<()> {
    let actual = String::from_utf8(cmd("hello.asm")?.stdout)?;
    let expected = read_file("hello.stdout")?;

    assert_eq!(actual, expected);
    Ok(())
}
