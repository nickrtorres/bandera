use std::io::stdin;
use std::io::BufRead;

use bandera::lex;
use bandera::parse;
use bandera::Vm;

fn repl() {
    let stdin = stdin();
    let mut handle = stdin.lock();

    let mut vm = Vm::new();
    loop {
        let mut buffer = String::with_capacity(1024);
        if handle.read_line(&mut buffer).expect("could not read line") == 0 {
            break;
        }

        let tokens = lex(buffer.chars().peekable());
        let ops = parse(tokens.into_iter().peekable());
        vm.run(ops).expect("uh-oh!");
    }
}

fn main() {
    repl();
}
