use std::error::Error;
use std::fs;
use std::process::{Command, Output};
use std::result;

type Result<T> = result::Result<T, Box<dyn Error>>;

fn cmd(name: &str) -> Result<Output> {
    let output = Command::new("./target/debug/bandera")
        .arg(format!("./tests/asm/dos/{}", name))
        .output()?;

    Ok(output)
}

fn read_file(name: &str) -> Result<String> {
    let data = fs::read_to_string(format!("./tests/output/dos/{}", name))?;
    Ok(data)
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
