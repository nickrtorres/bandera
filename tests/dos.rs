use std::error::Error;
use std::process::{Command, Output};
use std::result;

type Result<T> = result::Result<T, Box<dyn Error>>;

fn cmd(name: &str) -> Result<Output> {
    let output = Command::new("./target/debug/bandera")
        .arg(format!("./tests/asm/dos/{}", name))
        .output()?;

    Ok(output)
}

#[test]
fn exit() -> Result<()> {
    let output = cmd("exit.asm")?;
    assert_eq!(output.status.code(), Some(42 as i32));

    Ok(())
}
