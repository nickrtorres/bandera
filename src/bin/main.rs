use std::io::stdin;
use std::io::BufRead;

use bandera::lex;
use bandera::parse;
use bandera::Vm;

fn repl() {
    let stdin = stdin();
    let ops = parse(
        stdin
            .lock()
            .lines()
            .filter(Result::is_ok)
            .flat_map(|line| lex(line.unwrap().chars().peekable()))
            .peekable(),
    );

    let mut vm = Vm::new();
    vm.run(ops).expect("uh-oh!");
}

fn main() {
    repl();
}
