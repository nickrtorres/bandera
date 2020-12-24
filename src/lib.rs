use std::convert::TryInto;
use std::error::Error;
use std::iter::Peekable;
use std::str::Chars;

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum Token {
    Add,
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
}

pub fn lex(mut stream: Peekable<Chars>) -> Vec<Token> {
    let mut tokens = Vec::default();

    while let Some(c) = stream.next() {
        if c == '\n' || c == ',' || c == ' ' {
            continue;
        }

        if c == ';' {
            while let Some(c) = stream.next() {
                if c == '\n' {
                    break;
                }
            }

            continue;
        }

        match c {
            'm' => match stream.next() {
                Some('o') => match stream.next() {
                    Some('v') => tokens.push(Token::Mov),
                    _ => panic!("unexpected character"),
                },
                _ => panic!("unexpected character"),
            },

            'a' => match stream.next() {
                Some('x') => tokens.push(Token::Reg(RegisterTag::Ax)),
                Some('d') => {
                    if let Some('d') = stream.next() {
                        tokens.push(Token::Add);
                    }
                }
                _ => panic!("unknown token"),
            },
            'b' => match stream.next() {
                Some('x') => tokens.push(Token::Reg(RegisterTag::Bx)),
                _ => panic!("unknown token"),
            },
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
                    eprintln!("error: unexpected char: {}", c);
                }
            }
        };
    }

    tokens
}

pub fn parse<I: Iterator<Item = Token>>(mut tokens: Peekable<I>) -> Vec<Op> {
    fn mov<I: Iterator<Item = Token>>(stream: &mut Peekable<I>) -> Op {
        let dst = stream.next().unwrap().unwrap_reg();
        match stream.next() {
            Some(Token::Reg(src)) => Op::MovReg(dst, src),
            Some(Token::SignedImm(src)) => Op::MovImm(dst, src),
            Some(Token::UnsignedImm(src)) => Op::MovImm(dst, src.try_into().unwrap()),
            _ => panic!("invalid mov"),
        }
    }

    fn add<I: Iterator<Item = Token>>(stream: &mut Peekable<I>) -> Op {
        let dst = stream.next().unwrap().unwrap_reg();
        match stream.next() {
            Some(Token::Reg(src)) => Op::AddReg(dst, src),
            Some(Token::UnsignedImm(src)) => Op::AddImmUnsigned(dst, src),
            _ => panic!("invalid mov"),
        }
    }

    fn instr<I: Iterator<Item = Token>>(stream: &mut Peekable<I>) -> Op {
        match stream.next() {
            Some(Token::Mov) => mov(stream),
            Some(Token::Add) => add(stream),
            _ => panic!("uh-oh!"),
        }
    }

    let mut ops = Vec::default();
    while tokens.peek().is_some() {
        ops.push(instr(&mut tokens));
    }

    ops
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
    // FIXME maybe this doesn't belong here ...
    fn register_from_tag(&mut self, tag: RegisterTag) -> &mut Register;
}

pub struct Vm {
    ax: Register,
    bx: Register,
    cf: u8,
    af: u8,
    sf: u8,
    zf: u8,
    pf: u8,
    of: u8,
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
        }
    }

    pub fn run(&mut self, instructions: Vec<Op>) -> Result<(), Box<dyn Error>> {
        for instruction in instructions {
            instruction.eval(self);
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

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum Op {
    MovImm(RegisterTag, i16),
    MovReg(RegisterTag, RegisterTag),
    CmpImm(RegisterTag, i16),
    AddImmUnsigned(RegisterTag, u16),
    AddReg(RegisterTag, RegisterTag),
}

impl Op {
    pub fn eval<T: RegisterMachine>(self, machine: &mut T) {
        match self {
            Self::MovImm(dst, src) => machine.update_imm(dst, src),
            Self::MovReg(dst, src) => machine.update_reg(dst, src),
            Self::CmpImm(dst, src) => machine.compare_imm(dst, src),
            Self::AddImmUnsigned(dst, src) => machine.add_imm_unsigned(dst, src),
            Self::AddReg(dst, src) => machine.add_reg_unsigned(dst, src),
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
        let mut ops = parse(tokens.into_iter().peekable()).into_iter();
        assert_eq!(Some(Op::MovImm(RegisterTag::Ax, 42)), ops.next());
        assert_eq!(None, ops.next());
    }

    #[test]
    fn mov_imm() {
        let instructions = vec![Op::MovImm(RegisterTag::Ax, 42)];

        let mut vm = Vm::new();
        vm.run(instructions).expect("Invalid instruction");

        assert_eq!(vm.ax(), 42);
        assert_eq!(vm.bx(), 0);
    }

    #[test]
    fn mov_reg() {
        let instructions = vec![
            Op::MovImm(RegisterTag::Ax, 42),
            Op::MovReg(RegisterTag::Bx, RegisterTag::Ax),
        ];

        let mut vm = Vm::new();

        vm.run(instructions).expect("Invalid instruction");

        assert_eq!(vm.ax(), 42);
        assert_eq!(vm.bx(), 42);
    }

    #[test]
    fn add_imm() {
        let instructions = vec![
            Op::MovImm(RegisterTag::Ax, 42),
            Op::AddImmUnsigned(RegisterTag::Ax, 100),
        ];

        let mut vm = Vm::new();

        vm.run(instructions).expect("Invalid instruction");

        assert_eq!(vm.ax(), 142);
    }

    #[test]
    fn add_reg() {
        let instructions = vec![
            Op::MovImm(RegisterTag::Ax, 42),
            Op::MovImm(RegisterTag::Bx, 20),
            Op::AddReg(RegisterTag::Ax, RegisterTag::Bx),
        ];

        let mut vm = Vm::new();

        vm.run(instructions).expect("Invalid instruction");

        assert_eq!(vm.ax(), 62);
    }
}
