use std::env;
use std::fmt::Debug;
use std::fs::File;
use std::io::stdin;
use std::io::BufRead;
use std::io::BufReader;

use bandera::lex;
use bandera::Dos;
use bandera::Parser;
use bandera::Vm;

fn run<T: BufRead + Debug>(buf: T) {
    let program = Parser::new(
        buf.lines()
            .filter(Result::is_ok)
            .flat_map(|line| lex(line.unwrap().chars().peekable()))
            .peekable(),
    )
    .run();

    Vm::<Dos>::new().run(program).expect("uh-oh!");
}

fn main() {
    let args = env::args().collect::<Vec<String>>();
    if args.len() == 2 {
        run(BufReader::new(File::open(&args[1]).unwrap()));
    } else {
        run(stdin().lock());
    }
}
