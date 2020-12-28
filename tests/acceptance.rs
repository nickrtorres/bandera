use bandera::lex;
use bandera::MachineState;
use bandera::Parser;
use bandera::Register;
use bandera::Vm;
use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::result::Result;

fn run(name: &str) -> Result<MachineState, Box<dyn Error>> {
    let file = File::open(format!("tests/asm/{}", name))?;
    let program = Parser::new(
        BufReader::new(file)
            .lines()
            .filter(Result::is_ok)
            .flat_map(|line| lex(line.unwrap().chars().peekable()))
            .peekable(),
    )
    .run();

    Vm::new().run(program)
}

fn register_from(value: i16) -> Register {
    let mut reg = Register::new();
    reg.update(value);
    reg
}

#[test]
fn addition() -> Result<(), Box<dyn Error>> {
    let actual = run("addition.asm")?;
    let expected = MachineState {
        ax: register_from(84),
        bx: register_from(0),
    };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn je() -> Result<(), Box<dyn Error>> {
    let actual = run("je.asm")?;
    let expected = MachineState {
        ax: register_from(84),
        bx: register_from(0),
    };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn jne() -> Result<(), Box<dyn Error>> {
    let actual = run("jne.asm")?;
    let expected = MachineState {
        ax: register_from(84),
        bx: register_from(0),
    };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn simple_loop() -> Result<(), Box<dyn Error>> {
    let actual = run("simple_loop.asm")?;
    let expected = MachineState {
        ax: register_from(10),
        bx: register_from(0),
    };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn loop_with_call() -> Result<(), Box<dyn Error>> {
    let actual = run("loop_with_call.asm")?;
    let expected = MachineState {
        ax: register_from(32000),
        bx: register_from(0),
    };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn simple_procedure() -> Result<(), Box<dyn Error>> {
    let actual = run("simple_procedure.asm")?;
    let expected = MachineState {
        ax: register_from(42),
        bx: register_from(0),
    };

    assert_eq!(actual, expected);
    Ok(())
}

#[test]
fn call() -> Result<(), Box<dyn Error>> {
    let actual = run("call.asm")?;
    let expected = MachineState {
        ax: register_from(142),
        bx: register_from(0),
    };

    assert_eq!(actual, expected);
    Ok(())
}
