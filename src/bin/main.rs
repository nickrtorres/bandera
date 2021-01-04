use std::env;
use std::fmt::Debug;
use std::fs::File;
use std::io::stdin;
use std::io::BufRead;
use std::io::BufReader;

use bandera::core::lex;
use bandera::core::Dos;
use bandera::core::Parser;
use bandera::core::Program;
use bandera::core::Vm;

fn parse<T: BufRead + Debug>(buf: T) -> Program {
    Parser::new(
        buf.lines()
            .filter(Result::is_ok)
            .flat_map(|line| lex(line.unwrap().chars().peekable()))
            .peekable(),
    )
    .run()
}

fn repl() {
    let stdin = stdin();
    let program = parse(stdin.lock());
    let mut vm: Vm<Dos> = Vm::new();
    vm.run(program).expect("uh-oh!");
    vm.dump();
}

fn file(name: &str) {
    let f = File::open(name).unwrap();
    let reader = BufReader::new(f);
    let program = parse(reader);
    let mut vm: Vm<Dos> = Vm::new();
    vm.run(program).expect("uh-oh!");
    vm.dump();
}

fn main() {
    let args = env::args().collect::<Vec<String>>();
    if args.len() == 2 {
        file(&args[1]);
    } else {
        repl();
    }
}
