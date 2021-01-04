use bandera::core::lex;
use bandera::core::Dos;
use bandera::core::MachineState;
use bandera::core::Parser;
use bandera::core::Vm;
use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn run(name: &str) -> Result<MachineState> {
    let file = File::open(format!("tests/asm/{}", name))?;
    let program = Parser::new(
        BufReader::new(file)
            .lines()
            .filter(std::result::Result::is_ok)
            .flat_map(|line| lex(line.unwrap().chars().peekable()))
            .peekable(),
    )
    .run();

    Vm::<Dos>::new().run(program)
}

#[test]
fn addition() -> Result<()> {
    let actual = run("addition.asm")?;
    let expected = MachineState { ax: 84, bx: 0 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn je() -> Result<()> {
    let actual = run("je.asm")?;
    let expected = MachineState { ax: 84, bx: 0 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn jne() -> Result<()> {
    let actual = run("jne.asm")?;
    let expected = MachineState { ax: 84, bx: 0 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn simple_loop() -> Result<()> {
    let actual = run("simple_loop.asm")?;
    let expected = MachineState { ax: 10, bx: 0 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn loop_with_call() -> Result<()> {
    let actual = run("loop_with_call.asm")?;
    let expected = MachineState { ax: 32000, bx: 0 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn simple_procedure() -> Result<()> {
    let actual = run("simple_procedure.asm")?;
    let expected = MachineState { ax: 42, bx: 0 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn call() -> Result<()> {
    let actual = run("call.asm")?;
    let expected = MachineState { ax: 142, bx: 0 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn push() -> Result<()> {
    let actual = run("push.asm")?;
    let expected = MachineState { ax: 2, bx: 4 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn empty_procedure() -> Result<()> {
    let actual = run("empty_procedure.asm")?;
    let expected = MachineState { ax: 42, bx: 0 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn load_from_stack() -> Result<()> {
    let actual = run("load_from_stack.asm")?;
    let expected = MachineState { ax: 42, bx: 42 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn sub() -> Result<()> {
    let actual = run("sub.asm")?;
    let expected = MachineState { ax: 42, bx: 0 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn jge() -> Result<()> {
    let actual = run("jge.asm")?;
    let expected = MachineState { ax: 4, bx: 0 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn pop() -> Result<()> {
    let actual = run("pop.asm")?;
    let expected = MachineState { ax: 142, bx: 42 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn fib() -> Result<()> {
    let actual = run("fib.asm")?;
    let expected = MachineState { ax: 46368, bx: 0 };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn split_register() -> Result<()> {
    let actual = run("split_register.asm")?;
    let expected = MachineState {
        ax: 0xABCD,
        bx: 0x1234,
    };

    assert_eq!(actual, expected);
    Ok(())
}
