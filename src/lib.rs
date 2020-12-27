use std::collections::HashMap;
use std::convert::TryInto;
use std::error::Error;
use std::iter::Peekable;
use std::str::Chars;

#[derive(PartialEq, Debug)]
pub enum Token {
    Add,
    Cmp,
    Iden(String),
    Jmp,
    Jne,
    Label(String),
    Mov,
    Reg(RegisterTag),
    SignedImm(i16),
    UnsignedImm(u16),
}

impl Token {
    fn unwrap_reg(self) -> RegisterTag {
        match self {
            Self::Reg(r) => r,
            _ => panic!("not a register!"),
        }
    }

    fn unwrap_iden(self) -> String {
        match self {
            Self::Iden(i) => i,
            c => panic!("{:?} -- not an identifier", c),
        }
    }
}

pub fn lex(mut stream: Peekable<Chars>) -> Vec<Token> {
    let mut tokens = Vec::default();
    while let Some(c) = stream.next() {
        match c {
            '\n' | ',' | ' ' => {}
            ';' => {
                while let Some(c) = stream.next() {
                    if c == '\n' {
                        break;
                    }
                }

                continue;
            }
            '-' => {
                let mut buffer = String::from('-');
                while let Some(d) = stream.peek() {
                    if d.is_ascii_digit() {
                        buffer.push(stream.next().unwrap());
                    } else {
                        break;
                    }
                }
                tokens.push(Token::SignedImm(buffer.parse::<i16>().expect(
                    format!("{} is not a valid signed 16 bit integer", buffer).as_str(),
                )));
            }
            c => {
                if c.is_ascii_digit() {
                    let mut buffer = String::from(c);
                    while let Some(d) = stream.peek() {
                        if d.is_ascii_digit() {
                            buffer.push(stream.next().unwrap());
                        } else {
                            break;
                        }
                    }
                    tokens.push(Token::UnsignedImm(buffer.parse::<u16>().expect(
                        format!("{} is not a valid signed 16 bit integer", buffer).as_str(),
                    )));
                } else {
                    let mut scratch = String::from(c);
                    while let Some(c) = stream.next() {
                        if c == ',' || c == ' ' || c == '\n' {
                            break;
                        }

                        scratch.push(c);
                    }

                    if scratch.ends_with(":") {
                        scratch.pop();
                        tokens.push(Token::Label(scratch));
                        continue;
                    }

                    match scratch.as_str() {
                        "ax" => tokens.push(Token::Reg(RegisterTag::Ax)),
                        "bx" => tokens.push(Token::Reg(RegisterTag::Bx)),
                        "add" => tokens.push(Token::Add),
                        "cmp" => tokens.push(Token::Cmp),
                        "jmp" => tokens.push(Token::Jmp),
                        "jne" => tokens.push(Token::Jne),
                        "mov" => tokens.push(Token::Mov),
                        _ => tokens.push(Token::Iden(scratch)),
                    }
                }
            }
        };
    }

    tokens
}

type SymbolTable = HashMap<String, usize>;
pub struct Program(SymbolTable, Vec<Op>);

pub fn parse<I>(mut tokens: Peekable<I>) -> Program
where
    I: Iterator<Item = Token>,
{
    fn mov<I>(stream: &mut Peekable<I>) -> Option<Op>
    where
        I: Iterator<Item = Token>,
    {
        let dst = stream.next().unwrap().unwrap_reg();
        match stream.next() {
            Some(Token::Reg(src)) => Some(Op::MovReg(dst, src)),
            Some(Token::SignedImm(src)) => Some(Op::MovImm(dst, src)),
            Some(Token::UnsignedImm(src)) => Some(Op::MovImm(dst, src.try_into().unwrap())),
            _ => panic!("invalid mov"),
        }
    }

    fn add<I>(stream: &mut Peekable<I>) -> Option<Op>
    where
        I: Iterator<Item = Token>,
    {
        let dst = stream.next().unwrap().unwrap_reg();
        match stream.next() {
            Some(Token::Reg(src)) => Some(Op::AddReg(dst, src)),
            Some(Token::UnsignedImm(src)) => Some(Op::AddImmUnsigned(dst, src)),
            _ => panic!("invalid mov"),
        }
    }

    fn jmp<I>(stream: &mut Peekable<I>) -> Option<Op>
    where
        I: Iterator<Item = Token>,
    {
        let label = stream.next().unwrap().unwrap_iden();
        Some(Op::Jmp(label))
    }

    fn jne<I>(stream: &mut Peekable<I>) -> Option<Op>
    where
        I: Iterator<Item = Token>,
    {
        let label = stream.next().unwrap().unwrap_iden();
        Some(Op::Jne(label))
    }

    fn cmp<I>(stream: &mut Peekable<I>) -> Option<Op>
    where
        I: Iterator<Item = Token>,
    {
        let dst = stream.next().unwrap().unwrap_reg();
        match stream.next() {
            Some(Token::SignedImm(src)) => Some(Op::CmpImm(dst, src)),
            Some(Token::UnsignedImm(src)) => Some(Op::CmpImm(dst, src as i16)),
            c => todo!("{}", format!("{:?}", c)),
        }
    }

    fn instr<I>(stream: &mut Peekable<I>, label_stack: &mut Vec<String>) -> Option<Op>
    where
        I: Iterator<Item = Token>,
    {
        match stream.next() {
            Some(Token::Mov) => mov(stream),
            Some(Token::Add) => add(stream),
            Some(Token::Label(s)) => {
                label_stack.push(s);
                None
            }
            Some(Token::Jmp) => jmp(stream),
            Some(Token::Jne) => jne(stream),
            Some(Token::Cmp) => cmp(stream),
            c => panic!(format!("uh-oh! -- {:?}", c)),
        }
    }

    let mut ops = Vec::default();
    let mut symbol_table: SymbolTable = HashMap::new();
    let mut label_stack = Vec::default();

    while tokens.peek().is_some() {
        if let Some(label) = label_stack.pop() {
            symbol_table.insert(label, ops.len());
            assert_eq!(label_stack.len(), 0);
        }

        if let Some(op) = instr(&mut tokens, &mut label_stack) {
            ops.push(op);
        }
    }

    Program(symbol_table, ops)
}

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum RegisterTag {
    Ax,
    Bx,
}

// TODO: add register tag
#[derive(Debug)]
pub struct Register {
    // TODO: A _register_ can really be 8 or 16 bit (i.e. a 16 bit register can
    // split into two 8-bit registers).
    value: i16,
}

impl Register {
    fn new() -> Self {
        Register { value: 0 }
    }

    fn update(&mut self, src: i16) {
        self.value = src;
    }

    fn value(&self) -> i16 {
        self.value
    }
}

pub trait RegisterMachine {
    fn update_reg(&mut self, dst: RegisterTag, src: RegisterTag);
    fn update_imm(&mut self, dst: RegisterTag, src: i16);
    fn compare_imm(&mut self, reg: RegisterTag, value: i16);
    fn add_imm_unsigned(&mut self, reg: RegisterTag, value: u16);
    fn add_reg_unsigned(&mut self, dst: RegisterTag, src: RegisterTag);
    fn unconditional_jump(&mut self, label: &str);
    fn jump_not_equal(&mut self, label: &str);
    // FIXME maybe this doesn't belong here ...
    fn register_from_tag(&mut self, tag: RegisterTag) -> &mut Register;
}

#[derive(Debug)]
pub struct Vm {
    ax: Register,
    bx: Register,
    cf: u8,
    af: u8,
    sf: u8,
    zf: u8,
    pf: u8,
    of: u8,
    ip: usize,
    symbol_table: SymbolTable,
    jumped: bool,
}

impl RegisterMachine for Vm {
    fn update_reg(&mut self, dst: RegisterTag, src: RegisterTag) {
        let src = self.register_from_tag(src).value();
        let dst = self.register_from_tag(dst);
        dst.update(src);
    }

    fn update_imm(&mut self, dst: RegisterTag, src: i16) {
        let dst = self.register_from_tag(dst);
        dst.update(src);
    }

    // Updates AF, CF, OF, PF, SF, and ZF
    fn compare_imm(&mut self, dst: RegisterTag, src: i16) {
        let dst = self.register_from_tag(dst).value();

        let r = dst - src;

        // TODO
        // > If a subtraction results in a borrow into the high-order bit of
        //   the result, then CF is set; otherwise CF is cleared.
        // For now, just clear CF.
        self.cf = 0;
        self.af = 0;
        self.sf = (r <= 0) as u8;
        self.zf = (r == 0) as u8;

        // TODO: audit
        self.pf = (r.count_ones() % 2 == 0) as u8;
        self.of = 0;
    }

    fn add_imm_unsigned(&mut self, dst: RegisterTag, src: u16) {
        // TODO set flags
        let dst = self.register_from_tag(dst);
        dst.update(dst.value() + src as i16);
    }

    fn add_reg_unsigned(&mut self, dst: RegisterTag, src: RegisterTag) {
        // TODO set flags
        let src = self.register_from_tag(src).value();
        let dst = self.register_from_tag(dst);
        dst.update(dst.value() + src);
    }

    fn unconditional_jump(&mut self, label: &str) {
        // TODO: handle failure
        self.ip = *self.symbol_table.get(label).unwrap();
        self.jumped = true;
    }

    fn jump_not_equal(&mut self, label: &str) {
        if self.zf == 0 {
            // TODO: handle failure
            self.ip = *self.symbol_table.get(label).unwrap();
            self.jumped = true;
        }
    }

    fn register_from_tag(&mut self, tag: RegisterTag) -> &mut Register {
        match tag {
            RegisterTag::Ax => &mut self.ax,
            RegisterTag::Bx => &mut self.bx,
        }
    }
}

impl Vm {
    pub fn new() -> Self {
        Vm {
            ax: Register::new(),
            bx: Register::new(),
            cf: 0,
            af: 0,
            sf: 0,
            zf: 0,
            pf: 0,
            of: 0,
            ip: 0,
            symbol_table: HashMap::default(),
            jumped: false,
        }
    }

    pub fn run(&mut self, program: Program) -> Result<(), Box<dyn Error>> {
        let Program(symbols, instructions) = program;
        self.symbol_table = symbols;

        for op in instructions {
            op.eval(self);
        }

        Ok(())
    }

    pub fn ax(&self) -> i16 {
        self.ax.value()
    }

    pub fn bx(&self) -> i16 {
        self.bx.value()
    }

    pub fn dump(&self) {
        eprintln!("\n*******************************************");
        eprintln!("ax => [{:?}]", self.ax);
        eprintln!("bx => [{:?}]", self.bx);
        eprintln!("cf => [{:?}]", self.cf);
        eprintln!("af => [{:?}]", self.af);
        eprintln!("sf => [{:?}]", self.sf);
        eprintln!("zf => [{:?}]", self.zf);
        eprintln!("pf => [{:?}]", self.pf);
        eprintln!("of => [{:?}]", self.of);
        eprintln!("*******************************************\n");
    }
}

#[derive(PartialEq, Debug)]
pub enum Op {
    MovImm(RegisterTag, i16),
    MovReg(RegisterTag, RegisterTag),
    CmpImm(RegisterTag, i16),
    AddImmUnsigned(RegisterTag, u16),
    AddReg(RegisterTag, RegisterTag),
    Jmp(String),
    Jne(String),
}

impl Op {
    pub fn eval<T: RegisterMachine>(&self, machine: &mut T) {
        match self {
            Self::MovImm(dst, src) => machine.update_imm(*dst, *src),
            Self::MovReg(dst, src) => machine.update_reg(*dst, *src),
            Self::CmpImm(dst, src) => machine.compare_imm(*dst, *src),
            Self::AddImmUnsigned(dst, src) => machine.add_imm_unsigned(*dst, *src),
            Self::AddReg(dst, src) => machine.add_reg_unsigned(*dst, *src),
            Self::Jmp(label) => machine.unconditional_jump(label),
            Self::Jne(label) => machine.jump_not_equal(label),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_lex() {
        let mut tokens = lex("mov ax, 42".chars().peekable()).into_iter();
        assert_eq!(Some(Token::Mov), tokens.next());
        assert_eq!(Some(Token::Reg(RegisterTag::Ax)), tokens.next());
        assert_eq!(Some(Token::UnsignedImm(42)), tokens.next());
        assert_eq!(None, tokens.next());
    }

    #[test]
    fn lex_ignore_comments() {
        let mut tokens = lex("mov ax, 42 ; don't care".chars().peekable()).into_iter();
        assert_eq!(Some(Token::Mov), tokens.next());
        assert_eq!(Some(Token::Reg(RegisterTag::Ax)), tokens.next());
        assert_eq!(Some(Token::UnsignedImm(42)), tokens.next());
        assert_eq!(None, tokens.next());
    }

    #[test]
    fn simple_parse() {
        let tokens = lex("mov ax, 42".chars().peekable()).into_iter();
        let mut ops = parse(tokens.into_iter().peekable()).1.into_iter();
        assert_eq!(Some(Op::MovImm(RegisterTag::Ax, 42)), ops.next());
        assert_eq!(None, ops.next());
    }

    #[test]
    fn parse_labels() {
        let tokens = vec![
            Token::Add, // Op 0
            Token::Reg(RegisterTag::Ax),
            Token::Reg(RegisterTag::Bx),
            Token::Label("Foo".to_owned()),
            Token::Add, // Op 1
            Token::Reg(RegisterTag::Ax),
            Token::Reg(RegisterTag::Ax),
        ];
        let Program(symbols, _) = parse(tokens.into_iter().peekable());
        assert_eq!(symbols.get("Foo"), Some(&(1 as usize)));
    }

    #[test]
    fn mov_imm() {
        let program = Program(HashMap::default(), vec![Op::MovImm(RegisterTag::Ax, 42)]);

        let mut vm = Vm::new();
        vm.run(program).expect("Invalid instruction");

        assert_eq!(vm.ax(), 42);
        assert_eq!(vm.bx(), 0);
    }

    #[test]
    fn mov_reg() {
        let program = Program(
            HashMap::default(),
            vec![
                Op::MovImm(RegisterTag::Ax, 42),
                Op::MovReg(RegisterTag::Bx, RegisterTag::Ax),
            ],
        );

        let mut vm = Vm::new();

        vm.run(program).expect("Invalid instruction");

        assert_eq!(vm.ax(), 42);
        assert_eq!(vm.bx(), 42);
    }

    #[test]
    fn add_imm() {
        let program = Program(
            HashMap::default(),
            vec![
                Op::MovImm(RegisterTag::Ax, 42),
                Op::AddImmUnsigned(RegisterTag::Ax, 100),
            ],
        );

        let mut vm = Vm::new();

        vm.run(program).expect("Invalid instruction");

        assert_eq!(vm.ax(), 142);
    }

    #[test]
    fn add_reg() {
        let program = Program(
            HashMap::default(),
            vec![
                Op::MovImm(RegisterTag::Ax, 42),
                Op::MovImm(RegisterTag::Bx, 20),
                Op::AddReg(RegisterTag::Ax, RegisterTag::Bx),
            ],
        );

        let mut vm = Vm::new();

        vm.run(program).expect("Invalid instruction");

        assert_eq!(vm.ax(), 62);
    }
}
