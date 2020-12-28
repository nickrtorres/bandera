use std::io::stdin;
use std::io::BufRead;

use bandera::lex;
use bandera::Parser;
use bandera::Vm;

fn repl() {
    let stdin = stdin();
    let ops = Parser::new(
        stdin
            .lock()
            .lines()
            .filter(Result::is_ok)
            .flat_map(|line| lex(line.unwrap().chars().peekable()))
            .peekable(),
    )
    .run();

    let mut vm = Vm::new();
    vm.run(ops).expect("uh-oh!");
    vm.dump();
}

fn main() {
    repl();
}
