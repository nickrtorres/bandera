use std::collections::HashMap;
use std::convert::TryInto;
use std::error::Error;
use std::fmt::Debug;
use std::iter::Peekable;
use std::mem::discriminant;
use std::str::Chars;

// Ironically, the entry point to an assembler program is the symbol marked 'END'
const ENTRY_POINT: &str = "END";

#[derive(PartialEq, Debug)]
pub enum Token {
    Add,
    Call,
    Cmp,
    End,
    Endp,
    Iden(String),
    Je,
    Jmp,
    Jne,
    Label(String),
    Mov,
    Proc,
    Reg(RegisterTag),
    Ret,
    SignedImm(i16),
    UnsignedImm(u16),
}

impl Token {
    fn into_reg_unchecked(self) -> RegisterTag {
        match self {
            Self::Reg(r) => r,
            _ => panic!("not a register!"),
        }
    }

    fn into_iden_unchecked(self) -> String {
        match self {
            Self::Iden(i) => i,
            c => panic!("{:?} -- not an identifier", c),
        }
    }

    fn into_label_unchecked(self) -> String {
        match self {
            Self::Label(s) => s,
            c => panic!("{:?} -- not a label", c),
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
                        "call" => tokens.push(Token::Call),
                        "cmp" => tokens.push(Token::Cmp),
                        "end" => tokens.push(Token::End),
                        "endp" => tokens.push(Token::Endp),
                        "je" => tokens.push(Token::Je),
                        "jmp" => tokens.push(Token::Jmp),
                        "jne" => tokens.push(Token::Jne),
                        "mov" => tokens.push(Token::Mov),
                        "proc" => tokens.push(Token::Proc),
                        "ret" => tokens.push(Token::Ret),
                        _ => tokens.push(Token::Iden(scratch)),
                    }
                }
            }
        };
    }

    tokens
}

type SymbolTable = HashMap<String, u16>;

#[derive(Debug)]
pub struct Program(SymbolTable, Vec<Op>);

pub struct Parser<I: Iterator<Item = Token> + Debug> {
    tokens: Peekable<I>,
    symbol_table: SymbolTable,
    pending_symbol: Option<String>,
    ops: Vec<Op>,
}

impl<I: Iterator<Item = Token> + Debug> Parser<I> {
    pub fn new(tokens: Peekable<I>) -> Self {
        Parser {
            tokens,
            symbol_table: SymbolTable::default(),
            pending_symbol: None,
            ops: Vec::default(),
        }
    }

    fn expect(&mut self, expected: Token) {
        if !self.tokens.next().map_or(false, move |actual| {
            discriminant(&expected) == discriminant(&actual)
        }) {
            panic!();
        }
    }

    pub fn run(self) -> Program {
        self.program()
    }

    fn mov(&mut self) {
        self.tokens.next().unwrap(); // consume MOV
        let dst = self.tokens.next().unwrap().into_reg_unchecked();
        match self.tokens.next() {
            Some(Token::Reg(src)) => self.ops.push(Op::MovReg(dst, src)),
            Some(Token::UnsignedImm(src)) => {
                self.ops.push(Op::MovImm(dst, src.try_into().unwrap()))
            }
            _ => panic!("invalid mov"),
        }
    }

    fn add(&mut self) {
        self.tokens.next().unwrap(); // consume ADD
        let dst = self.tokens.next().unwrap().into_reg_unchecked();
        match self.tokens.next() {
            Some(Token::Reg(src)) => self.ops.push(Op::AddReg(dst, src)),
            Some(Token::UnsignedImm(src)) => self.ops.push(Op::AddImmUnsigned(dst, src)),
            _ => panic!("invalid mov"),
        }
    }

    fn call(&mut self) {
        self.tokens.next().unwrap(); // consume CALL
        let proc = self.tokens.next().unwrap().into_iden_unchecked();
        self.ops.push(Op::Call(proc));
    }

    fn jump(&mut self, j: Token, label: Token) {
        let label = label.into_iden_unchecked();
        match j {
            Token::Jmp => self.ops.push(Op::Jmp(label)),
            Token::Jne => self.ops.push(Op::Jne(label)),
            Token::Je => self.ops.push(Op::Je(label)),
            _ => panic!("expected jump not => {:?}", j),
        }
    }

    fn cmp(&mut self) {
        self.tokens.next().unwrap(); // consume CMP
        let dst = self.tokens.next().unwrap().into_reg_unchecked();
        match self.tokens.next() {
            Some(Token::UnsignedImm(src)) => self.ops.push(Op::CmpImm(dst, src as u16)),
            c => todo!("{}", format!("{:?}", c)),
        }
    }

    fn instr(&mut self) {
        if let Some(label) = self.pending_symbol.take() {
            self.symbol_table
                .insert(label, self.ops.len().try_into().unwrap());
        }

        match self.tokens.peek() {
            Some(Token::Mov) => self.mov(),
            Some(Token::Add) => self.add(),
            Some(Token::Call) => self.call(),
            Some(Token::Cmp) => self.cmp(),
            Some(Token::Jmp) | Some(Token::Jne) | Some(Token::Je) => {
                let token = self.tokens.next().unwrap();
                let next = self.tokens.next().unwrap();
                self.jump(token, next)
            }
            _ => {}
        }
    }

    // TODO clean this up
    fn label(&mut self) {
        let iden = self.tokens.next().unwrap().into_label_unchecked();
        assert!(self.pending_symbol.is_none());
        self.pending_symbol = Some(iden);
    }

    fn instr_list(&mut self) {
        match self.tokens.peek() {
            Some(Token::Ret) | Some(Token::End) | Some(Token::Iden(_)) | None => {}
            Some(token) => {
                if let Token::Label(_) = token {
                    self.label();
                }

                self.instr();
                self.instr_list();
            }
        }
    }

    fn procedure(&mut self) {
        // TODO add a declare / define symbol methods
        let iden = self.tokens.next().unwrap().into_iden_unchecked();
        assert!(self.pending_symbol.is_none());
        self.pending_symbol = Some(iden);

        self.tokens.next().unwrap(); // consume PROC

        self.instr_list();

        self.expect(Token::Ret);
        self.ops.push(Op::Ret);

        self.expect(Token::Iden(String::default()));
        self.expect(Token::Endp);
    }

    fn stmt_list(&mut self) {
        if let Some(Token::Iden(_)) = self.tokens.peek() {
            self.procedure();
        }

        self.instr_list();
    }

    fn end(&mut self) {
        self.expect(Token::End);
        let symbol = self.tokens.next().unwrap().into_iden_unchecked();
        let offset = *self.symbol_table.get(&symbol).unwrap();
        self.symbol_table.insert(ENTRY_POINT.to_owned(), offset);
    }

    fn program(mut self) -> Program {
        self.stmt_list();
        self.end();
        self.ops.push(Op::Halt);
        Program(self.symbol_table, self.ops)
    }
}

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum RegisterTag {
    Ax,
    Bx,
}

// TODO: add register tag
#[derive(Debug, PartialEq, Copy, Clone)]
pub struct Register {
    // TODO: A _register_ can really be 8 or 16 bit (i.e. a 16 bit register can
    // split into two 8-bit registers).
    value: u16,
}

impl Register {
    pub fn new() -> Self {
        Register { value: 0 }
    }

    pub fn update(&mut self, src: u16) {
        self.value = src;
    }

    fn value(&self) -> u16 {
        self.value
    }
}

pub trait AbstractMachine {
    fn update_reg(&mut self, dst: RegisterTag, src: RegisterTag);
    fn update_imm(&mut self, dst: RegisterTag, src: u16);
    fn compare_imm(&mut self, reg: RegisterTag, value: u16);
    fn add_imm_unsigned(&mut self, reg: RegisterTag, value: u16);
    fn add_reg_unsigned(&mut self, dst: RegisterTag, src: RegisterTag);
    fn unconditional_jump(&mut self, label: &str);
    fn jump_not_equal(&mut self, label: &str);
    fn jump_equal(&mut self, label: &str);
    fn ret(&mut self);
    fn call(&mut self, proc: &str);
    fn halt(&mut self);
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
    // It'd be _a lot_ nicer if these --ip and sp -- were usize so that indexing wouldn't require
    // explicit casts. But then the instruction pointer would require a cast to push it onto the
    // runtime stack.
    ip: u16,
    sp: Option<u16>,
    bp: usize,
    symbol_table: SymbolTable,
    stack: Vec<u16>,
    stack_limit: u16,
    halt: bool,
}

impl AbstractMachine for Vm {
    fn update_reg(&mut self, dst: RegisterTag, src: RegisterTag) {
        let src = self.register_from_tag(src).value();
        let dst = self.register_from_tag(dst);
        dst.update(src);
    }

    fn update_imm(&mut self, dst: RegisterTag, src: u16) {
        let dst = self.register_from_tag(dst);
        dst.update(src);
    }

    // Updates AF, CF, OF, PF, SF, and ZF
    fn compare_imm(&mut self, dst: RegisterTag, src: u16) {
        let dst = self.register_from_tag(dst).value();

        // hmmmmmmmmmmmmmmm
        let r = (dst as i16) - (src as i16);

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
        dst.update(dst.value() + src as u16);
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
    }

    fn jump_not_equal(&mut self, label: &str) {
        if self.zf == 0 {
            // TODO: handle failure
            self.ip = *self.symbol_table.get(label).unwrap();
        }
    }

    fn jump_equal(&mut self, label: &str) {
        if self.zf == 1 {
            // TODO: handle failure
            self.ip = *self.symbol_table.get(label).unwrap();
        }
    }

    fn ret(&mut self) {
        self.ip = self.pop();
    }

    fn call(&mut self, proc: &str) {
        self.push(self.ip);
        self.ip = *self.symbol_table.get(proc).unwrap();
    }

    fn halt(&mut self) {
        self.halt = true;
    }

    fn register_from_tag(&mut self, tag: RegisterTag) -> &mut Register {
        match tag {
            RegisterTag::Ax => &mut self.ax,
            RegisterTag::Bx => &mut self.bx,
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct MachineState {
    pub ax: Register,
    pub bx: Register,
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
            sp: None,
            bp: 0,
            symbol_table: HashMap::default(),
            stack: vec![0; 1024],
            stack_limit: 1024,
            halt: false,
        }
    }

    pub fn run(&mut self, program: Program) -> Result<MachineState, Box<dyn Error>> {
        let Program(symbols, instructions) = program;
        self.symbol_table = symbols;
        self.ip = *self.symbol_table.get(ENTRY_POINT).unwrap();

        while !self.halt {
            let op = instructions.get(self.ip() as usize).unwrap();
            op.eval(self);
        }

        Ok(self.state())
    }

    pub fn ip(&mut self) -> u16 {
        let instruction_pointer = self.ip;
        self.ip = self.ip + 1;
        instruction_pointer
    }

    pub fn dump(&self) {
        eprintln!("{:?}", self.state());
    }

    pub fn state(&self) -> MachineState {
        MachineState {
            ax: self.ax,
            bx: self.bx,
        }
    }

    //
    // `push` and `pop` follow the historical convention of growing downward and upward
    // respectively. This differs from standard `stack` conventions but is expected in _nominal_
    // assembler programming.
    //

    fn push(&mut self, value: u16) {
        let limit = self.stack_limit - 1;
        let sp = match self.sp {
            Some(0) => panic!("stack overflow!"),
            Some(sp) => {
                self.sp = Some(sp - 1);
                sp - 1
            }
            None => {
                self.sp = Some(limit);
                limit
            }
        };

        self.stack[sp as usize] = value;
    }

    fn pop(&mut self) -> u16 {
        let limit = self.stack_limit - 1;
        let st = match self.sp {
            Some(t) if t == limit => self.sp.take().unwrap(),
            Some(t) => {
                self.sp = Some(t + 1);
                t
            }
            None => panic!("stack underflow"),
        };

        self.stack[st as usize]
    }
}

#[derive(PartialEq, Debug)]
pub enum Op {
    MovImm(RegisterTag, u16),
    MovReg(RegisterTag, RegisterTag),
    CmpImm(RegisterTag, u16),
    AddImmUnsigned(RegisterTag, u16),
    AddReg(RegisterTag, RegisterTag),
    Jmp(String),
    Je(String),
    Jne(String),
    Ret,
    Call(String),
    Halt, //< Implementation detail
}

impl Op {
    pub fn eval<T: AbstractMachine>(&self, machine: &mut T) {
        match self {
            Self::MovImm(dst, src) => machine.update_imm(*dst, *src),
            Self::MovReg(dst, src) => machine.update_reg(*dst, *src),
            Self::CmpImm(dst, src) => machine.compare_imm(*dst, *src),
            Self::AddImmUnsigned(dst, src) => machine.add_imm_unsigned(*dst, *src),
            Self::AddReg(dst, src) => machine.add_reg_unsigned(*dst, *src),
            Self::Jmp(label) => machine.unconditional_jump(label),
            Self::Jne(label) => machine.jump_not_equal(label),
            Self::Je(label) => machine.jump_equal(label),
            Self::Ret => machine.ret(),
            Self::Call(proc) => machine.call(proc),
            Self::Halt => machine.halt(),
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
        let tokens = lex("main:\nmov ax, 42\nend main".chars().peekable()).into_iter();
        let mut ops = Parser::new(tokens.into_iter().peekable())
            .run()
            .1
            .into_iter();
        assert_eq!(Some(Op::MovImm(RegisterTag::Ax, 42)), ops.next());
        assert_eq!(Some(Op::Halt), ops.next());
        assert_eq!(None, ops.next());
    }

    #[test]
    fn parse_labels() {
        let tokens = vec![
            Token::Label(String::from("main")),
            Token::Add, // Op 0
            Token::Reg(RegisterTag::Ax),
            Token::Reg(RegisterTag::Bx),
            Token::Label("Foo".to_owned()),
            Token::Add, // Op 1
            Token::Reg(RegisterTag::Ax),
            Token::Reg(RegisterTag::Ax),
            Token::End,
            Token::Iden(String::from("main")),
        ];
        let Program(symbols, _) = Parser::new(tokens.into_iter().peekable()).run();
        assert_eq!(symbols.get("Foo"), Some(&(1)));
    }
}
