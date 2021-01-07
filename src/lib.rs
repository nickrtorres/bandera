use std::collections::HashMap;
use std::convert::TryFrom;
use std::convert::TryInto;
use std::error::Error;
use std::fmt::Debug;
use std::iter::Peekable;
use std::mem::discriminant;
use std::str::Chars;

mod interrupt;
use interrupt::Interrupt;

pub type Dos = interrupt::Dos;

const ENTRY_POINT: &str = "END";
const STACK_SIZE: u16 = 1024;

#[derive(PartialEq, Debug)]
pub enum Token {
    Add,
    Call,
    Cmp,
    Comma,
    DataSegment,
    Db,
    End,
    Endp,
    Iden(String),
    Int,
    Je,
    Jge,
    Jmp,
    Jne,
    Label(String),
    LeftBracket,
    Minus,
    Mov,
    Plus,
    Pop,
    Proc,
    Ptr,
    Push,
    QuestionMark,
    Reg(RegisterTag),
    Ret,
    RightBracket,
    SignedImm(i16),
    String(String),
    Sub,
    UnsignedImm(u16),
    Word,
}

impl TryFrom<Token> for RegisterTag {
    // TODO update this to a BanderaError when error handling is added.
    type Error = String;

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value {
            Token::Reg(r) => Ok(r),
            c => Err(format!("{:?} -- not a register!", c)),
        }
    }
}

impl TryFrom<Token> for String {
    // TODO update this to a BanderaError when error handling is added.
    type Error = String;

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value {
            Token::Label(s) | Token::Iden(s) => Ok(s),
            c => Err(format!("{:?} -- not a string!", c)),
        }
    }
}

impl TryFrom<Token> for u16 {
    // TODO update this to a BanderaError when error handling is added.
    type Error = String;

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value {
            Token::UnsignedImm(n) => Ok(n),
            c => Err(format!("{:?} -- not an unsigned immediate", c)),
        }
    }
}

pub fn lex(mut stream: Peekable<Chars>) -> Vec<Token> {
    let mut tokens = Vec::default();
    while let Some(c) = stream.next() {
        match c {
            '\n' | ' ' => {}
            ',' => tokens.push(Token::Comma),
            '+' => tokens.push(Token::Plus),
            '[' => tokens.push(Token::LeftBracket),
            ']' => tokens.push(Token::RightBracket),
            '?' => tokens.push(Token::QuestionMark),
            ';' => {
                while let Some(c) = stream.next() {
                    if c == '\n' {
                        break;
                    }
                }

                continue;
            }
            '-' => {
                if let Some(' ') = stream.peek() {
                    tokens.push(Token::Minus);
                    continue;
                }

                let mut buffer = String::from('-');
                while let Some(d) = stream.peek() {
                    if d.is_ascii_digit() {
                        buffer.push(stream.next().unwrap());
                    } else {
                        break;
                    }
                }
                tokens.push(Token::SignedImm(buffer.parse::<i16>().unwrap()));
            }
            '\'' => {
                let mut scratch = String::new();
                while let Some(c) = stream.peek().copied() {
                    if c == '\'' {
                        break;
                    } else {
                        scratch.push(stream.next().unwrap());
                    }
                }

                tokens.push(Token::String(scratch));
            }
            c => {
                let mut scratch = String::from(c);
                while let Some(c) = stream.peek().copied() {
                    if c == ',' || c == ']' || c == '[' || c == ',' || c == ' ' || c == '\n' {
                        break;
                    }

                    stream.next();
                    scratch.push(c);
                }

                // TODO fail if string is not ascii
                scratch.make_ascii_lowercase();

                if scratch.ends_with(':') {
                    scratch.pop();
                    tokens.push(Token::Label(scratch));
                    continue;
                }

                // Hex digits come in two forms:
                // (1) prefixed with "0x"
                // (2) suffixed with 'h' # NB this one seems to carry some DOS history
                //
                // TODO This is slow. Maaaaybe use regex here instead.

                match scratch.as_str() {
                    "ax" => tokens.push(Token::Reg(RegisterTag::Ax)),
                    "ah" => tokens.push(Token::Reg(RegisterTag::Ah)),
                    "al" => tokens.push(Token::Reg(RegisterTag::Al)),
                    "bx" => tokens.push(Token::Reg(RegisterTag::Bx)),
                    "bh" => tokens.push(Token::Reg(RegisterTag::Bh)),
                    "bl" => tokens.push(Token::Reg(RegisterTag::Bl)),
                    "dx" => tokens.push(Token::Reg(RegisterTag::Dx)),
                    "dh" => tokens.push(Token::Reg(RegisterTag::Dh)),
                    "dl" => tokens.push(Token::Reg(RegisterTag::Dl)),
                    "bp" => tokens.push(Token::Reg(RegisterTag::Bp)),
                    "sp" => tokens.push(Token::Reg(RegisterTag::Sp)),
                    ".data" => tokens.push(Token::DataSegment),
                    "add" => tokens.push(Token::Add),
                    "call" => tokens.push(Token::Call),
                    "cmp" => tokens.push(Token::Cmp),
                    "db" => tokens.push(Token::Db),
                    "end" => tokens.push(Token::End),
                    "endp" => tokens.push(Token::Endp),
                    "int" => tokens.push(Token::Int),
                    "je" => tokens.push(Token::Je),
                    "jge" => tokens.push(Token::Jge),
                    "jmp" => tokens.push(Token::Jmp),
                    "jne" => tokens.push(Token::Jne),
                    "mov" => tokens.push(Token::Mov),
                    "pop" => tokens.push(Token::Pop),
                    "proc" => tokens.push(Token::Proc),
                    "ptr" => tokens.push(Token::Ptr),
                    "push" => tokens.push(Token::Push),
                    "ret" => tokens.push(Token::Ret),
                    "sub" => tokens.push(Token::Sub),
                    "word" => tokens.push(Token::Word),
                    s => {
                        let is_valid_hex = |hex: &str| hex.chars().all(|c| c.is_ascii_hexdigit());
                        if s.ends_with('h') && is_valid_hex(&s[0..s.len() - 1]) {
                            tokens.push(Token::UnsignedImm(
                                u16::from_str_radix(&s[0..s.len() - 1], 16).unwrap(),
                            ));
                        } else if s.starts_with("0x") && is_valid_hex(&s[2..s.len()]) {
                            tokens.push(Token::UnsignedImm(
                                u16::from_str_radix(&s[2..s.len()], 16).unwrap(),
                            ));
                        } else if s.chars().all(|c| c.is_ascii_digit()) {
                            tokens.push(Token::UnsignedImm(u16::from_str_radix(s, 10).unwrap()));
                        } else {
                            tokens.push(Token::Iden(scratch));
                        }
                    }
                }
            }
        };
    }

    tokens
}

#[derive(Debug, Clone)]
enum DefinedByte {
    Sequence(Vec<ByteType>),
    Scalar(ByteType),
}

#[derive(Debug, Clone)]
enum ByteType {
    Byte(u8),
    String(String),
    Unitialized, //< ? character
}

impl TryFrom<Token> for ByteType {
    // TODO update this to a BanderaError when error handling is added.
    type Error = String;

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value {
            Token::String(s) => Ok(ByteType::String(s)),
            Token::QuestionMark => Ok(ByteType::Unitialized),
            Token::UnsignedImm(n) => Ok(ByteType::Byte(n.try_into().unwrap())),
            c => Err(format!("Error -- cannot convert {:?} into a ByteType", c)),
        }
    }
}

type SymbolTable = HashMap<String, u16>;
type DataTable = HashMap<String, DefinedByte>;

#[derive(Debug)]
pub struct Program(SymbolTable, DataTable, Vec<Op>);

pub struct Parser<I: Iterator<Item = Token> + Debug> {
    tokens: Peekable<I>,
    symbol_table: SymbolTable,
    data_table: DataTable,
    pending_symbol: Option<String>,
    ops: Vec<Op>,
}

impl<I: Iterator<Item = Token> + Debug> Parser<I> {
    pub fn new(tokens: Peekable<I>) -> Self {
        Parser {
            tokens,
            symbol_table: SymbolTable::default(),
            data_table: DataTable::default(),
            pending_symbol: None,
            ops: Vec::default(),
        }
    }

    fn expect(&mut self, expected: Token) {
        if !self.tokens.next().map_or(false, |actual| {
            discriminant(&expected) == discriminant(&actual)
        }) {
            panic!("Expected => {:?}", expected);
        }
    }

    pub fn run(self) -> Program {
        self.program()
    }

    fn mov(&mut self) {
        self.expect(Token::Mov);
        let dst = RegisterTag::try_from(self.tokens.next().unwrap()).unwrap();

        self.expect(Token::Comma);

        match self.tokens.next() {
            Some(Token::Reg(src)) => self.ops.push(Op::MovReg(dst, src)),
            Some(Token::UnsignedImm(src)) => self.ops.push(Op::MovImm(dst, src)),
            Some(Token::Iden(s)) => self.ops.push(Op::MovVar(dst, s)),
            Some(Token::Word) => {
                self.expect(Token::Ptr);
                self.expect(Token::LeftBracket);

                let src = self.tokens.next().unwrap().try_into().unwrap();
                let offset = match self.tokens.peek() {
                    Some(Token::Plus) => {
                        self.expect(Token::Plus);
                        let offset: u16 = self.tokens.next().unwrap().try_into().unwrap();
                        assert_eq!(0, offset % 2);
                        Some((OffsetOp::Add, offset / 2))
                    }
                    Some(Token::Minus) => {
                        self.expect(Token::Minus);
                        let offset: u16 = self.tokens.next().unwrap().try_into().unwrap();
                        assert_eq!(0, offset % 2);
                        Some((OffsetOp::Subtract, offset / 2))
                    }
                    _ => None,
                };

                self.expect(Token::RightBracket);
                self.ops.push(Op::MovMem(dst, src, offset))
            }
            t => panic!("{:?} -- invalid mov", t),
        }
    }

    fn add(&mut self) {
        self.expect(Token::Add);
        let dst = RegisterTag::try_from(self.tokens.next().unwrap()).unwrap();
        self.expect(Token::Comma);
        match self.tokens.next() {
            Some(Token::Reg(src)) => self.ops.push(Op::AddReg(dst, src)),
            Some(Token::UnsignedImm(src)) => self.ops.push(Op::AddImmUnsigned(dst, src)),
            _ => panic!("invalid mov"),
        }
    }

    fn call(&mut self) {
        self.expect(Token::Call);
        let proc = self.tokens.next().unwrap().try_into().unwrap();
        self.ops.push(Op::Call(proc));
    }

    fn jump(&mut self, j: Token, label: Token) {
        match j {
            Token::Jmp => self.ops.push(Op::Jmp(label.try_into().unwrap())),
            Token::Jne => self.ops.push(Op::Jne(label.try_into().unwrap())),
            Token::Jge => self.ops.push(Op::Jge(label.try_into().unwrap())),
            Token::Je => self.ops.push(Op::Je(label.try_into().unwrap())),
            _ => panic!("expected jump not => {:?}", j),
        }
    }

    fn cmp(&mut self) {
        self.expect(Token::Cmp);
        let dst = RegisterTag::try_from(self.tokens.next().unwrap()).unwrap();
        self.expect(Token::Comma);
        match self.tokens.next() {
            Some(Token::UnsignedImm(src)) => self.ops.push(Op::CmpImm(dst, src as u16)),
            c => todo!("{}", format!("{:?}", c)),
        }
    }

    fn push(&mut self) {
        self.expect(Token::Push);
        let src = RegisterTag::try_from(self.tokens.next().unwrap()).unwrap();
        self.ops.push(Op::Push(src));
    }

    fn pop(&mut self) {
        self.expect(Token::Pop);
        let src = RegisterTag::try_from(self.tokens.next().unwrap()).unwrap();
        self.ops.push(Op::Pop(src));
    }

    fn sub(&mut self) {
        self.expect(Token::Sub);
        let dst = RegisterTag::try_from(self.tokens.next().unwrap()).unwrap();
        self.expect(Token::Comma);
        match self.tokens.next() {
            Some(Token::UnsignedImm(src)) => self.ops.push(Op::SubImm(dst, src)),
            _ => panic!("invalid sub"),
        }
    }

    fn int(&mut self) {
        self.expect(Token::Int);
        let vector = u16::try_from(self.tokens.next().unwrap()).unwrap();
        self.ops.push(Op::Int(vector));
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
            Some(Token::Push) => self.push(),
            Some(Token::Pop) => self.pop(),
            Some(Token::Sub) => self.sub(),
            Some(Token::Int) => self.int(),
            Some(Token::Jmp) | Some(Token::Jne) | Some(Token::Je) | Some(Token::Jge) => {
                let token = self.tokens.next().unwrap();
                let next = self.tokens.next().unwrap();
                self.jump(token, next)
            }
            _ => {}
        }
    }

    // TODO clean this up
    fn label(&mut self) {
        let iden = String::try_from(self.tokens.next().unwrap()).unwrap();
        assert!(self.pending_symbol.is_none());
        self.pending_symbol = Some(iden);
    }

    fn instr_list(&mut self) {
        match self.tokens.peek() {
            Some(Token::Ret) => {
                if let Some(label) = self.pending_symbol.take() {
                    self.symbol_table
                        .insert(label, self.ops.len().try_into().unwrap());
                }
            }
            Some(Token::End) | Some(Token::Iden(_)) | None => {}
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
        let iden = String::try_from(self.tokens.next().unwrap()).unwrap();
        assert!(self.pending_symbol.is_none());
        self.pending_symbol = Some(iden);

        self.expect(Token::Proc);

        self.instr_list();

        self.expect(Token::Ret);

        let word_count = if let Some(Token::UnsignedImm(n)) = self.tokens.peek() {
            let count = *n;
            self.expect(Token::UnsignedImm(0));
            assert_eq!(0, count % 2);
            count / 2
        } else {
            0
        };

        self.ops.push(Op::Ret(word_count));
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
        let symbol = String::try_from(self.tokens.next().unwrap()).unwrap();
        let offset = *self.symbol_table.get(&symbol).unwrap();
        self.symbol_table.insert(ENTRY_POINT.to_owned(), offset);
    }

    fn data_directive(&mut self) {
        let var = String::try_from(self.tokens.next().unwrap()).unwrap();
        self.expect(Token::Db);

        let byte = ByteType::try_from(self.tokens.next().unwrap()).unwrap();
        if let Some(Token::Comma) = self.tokens.peek() {
            //
            // At this point the parser has encountered a sequence of bytes
            // defined by the programmer, e.g.
            // MY_VAR     DB    42, 100, 1000
            //
            // Our state at this point looks something like this.
            // MY_VAR     DB    42 , 100 , 1000
            //                   ^ ^
            //                   | |
            //                   + |
            //                  /  +--- self.tokens.next()
            //               byte
            //
            let mut sequence = Vec::new();
            sequence.push(byte);

            loop {
                self.expect(Token::Comma);

                sequence.push(self.tokens.next().unwrap().try_into().unwrap());
                if let Some(Token::Comma) = self.tokens.peek() {
                    continue;
                } else {
                    break;
                }
            }

            self.data_table.insert(var, DefinedByte::Sequence(sequence));
        } else {
            self.data_table.insert(var, DefinedByte::Scalar(byte));
        }
    }

    fn data_directive_list(&mut self) {
        if let Some(Token::Iden(_)) = self.tokens.peek() {
            self.data_directive();
            self.data_directive_list();
        }
    }

    fn data_segment(&mut self) {
        self.expect(Token::DataSegment);
        self.data_directive_list();
    }

    fn program(mut self) -> Program {
        if let Some(Token::DataSegment) = self.tokens.peek() {
            self.data_segment();
        }

        self.stmt_list();
        self.end();
        self.ops.push(Op::Halt);
        Program(self.symbol_table, self.data_table, self.ops)
    }
}

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum RegisterTag {
    Ax,
    Ah,
    Al,
    Bx,
    Bh,
    Bl,
    Dx,
    Dh,
    Dl,
    Bp,
    Sp,
}

#[derive(Debug, PartialEq)]
pub enum OffsetOp {
    Add,
    Subtract,
}

pub trait AbstractMachine {
    fn add_imm_unsigned(&mut self, reg: RegisterTag, value: u16);
    fn add_reg_unsigned(&mut self, dst: RegisterTag, src: RegisterTag);
    fn call(&mut self, proc: &str);
    fn compare_imm(&mut self, reg: RegisterTag, value: u16);
    fn jump_equal(&mut self, label: &str);
    fn jump_not_equal(&mut self, label: &str);
    fn jump_gt_equal(&mut self, label: &str);
    fn push_reg(&mut self, src: RegisterTag);
    fn pop_reg(&mut self, dst: RegisterTag);
    fn ret(&mut self, n: u16);
    fn sub_imm(&mut self, dst: RegisterTag, src: u16);
    fn unconditional_jump(&mut self, label: &str);
    fn update_imm(&mut self, dst: RegisterTag, src: u16);
    fn update_reg(&mut self, dst: RegisterTag, src: RegisterTag);
    fn update_reg_from_mem(
        &mut self,
        dst: RegisterTag,
        src: RegisterTag,
        offset: &Option<(OffsetOp, u16)>,
    );
    fn update_reg_from_var(&mut self, dst: RegisterTag, var: &str);
    fn interrupt(&mut self, vector: u16);
    fn halt(&mut self);
}

/// FullViewRegister provides an API to address the upper and lower bytes of a
/// 16-bit integer in little endian form.
#[derive(Debug)]
struct FullViewRegister {
    contents: [u8; 2],
}

impl FullViewRegister {
    pub fn new() -> Self {
        FullViewRegister {
            contents: [0x000, 0x0000],
        }
    }

    pub fn high(&self) -> u8 {
        self.contents[1]
    }

    pub fn low(&self) -> u8 {
        self.contents[0]
    }

    pub fn set_high(&mut self, byte: u8) {
        self.contents[1] = byte;
    }

    pub fn set_low(&mut self, byte: u8) {
        self.contents[0] = byte;
    }

    pub fn set_full(&mut self, bytes: u16) {
        self.contents = bytes.to_le_bytes();
    }

    pub fn full(&self) -> u16 {
        u16::from_le_bytes(self.contents)
    }
}

#[derive(Debug)]
pub struct Vm<H: Interrupt + Default> {
    ax: FullViewRegister,
    bx: FullViewRegister,
    dx: FullViewRegister,
    bp: u16,
    cf: u8,
    af: u8,
    sf: u8,
    zf: u8,
    pf: u8,
    of: u8,
    // It'd be _a lot_ nicer if these --ip and sp -- were usize so that indexing
    // wouldn't require explicit casts. But then the instruction pointer would
    // require a cast to push it onto the runtime stack.
    ip: u16,
    sp: Option<u16>,
    symbol_table: SymbolTable,
    data_table: DataTable,
    stack: Vec<u16>,
    stack_limit: u16,
    interrupt_handler: H,
    halt: bool,
}

impl<H: Interrupt + Default> AbstractMachine for Vm<H> {
    fn update_reg(&mut self, dst: RegisterTag, src: RegisterTag) {
        self.store(dst, self.load(src));
    }

    fn update_imm(&mut self, dst: RegisterTag, src: u16) {
        self.store(dst, src);
    }

    fn update_reg_from_mem(
        &mut self,
        dst: RegisterTag,
        src: RegisterTag,
        offset: &Option<(OffsetOp, u16)>,
    ) {
        // TODO bounds checking, error handling, etc
        let src = self.load(src);

        let value = match offset {
            Some((OffsetOp::Add, n)) => self.stack[(src + *n) as usize],
            Some((OffsetOp::Subtract, n)) => self.stack[(src - *n) as usize],
            None => self.stack[src as usize],
        };

        self.update_imm(dst, value);
    }

    fn update_reg_from_var(&mut self, dst: RegisterTag, var: &str) {
        // Audit cloning here
        match self.data_table.get(var).cloned() {
            Some(DefinedByte::Scalar(ByteType::Byte(src))) => self.store(dst, src as u16),
            Some(DefinedByte::Sequence(v)) => eprintln!("{:?}", v),
            _ => todo!(),
        }
    }

    // TODO:
    // This, along with the other arithmetic routines, should probably move into
    // an ALU module. The virtual machine would then call into the ALU and set
    // its flags based on the state / output of the ALU.
    //
    // Updates AF, CF, OF, PF, SF, and ZF
    fn compare_imm(&mut self, dst: RegisterTag, src: u16) {
        let dst = self.load(dst);

        // hmmmmmmmmmmmmmmm
        let y = (dst as i16) - (src as i16);

        // TODO
        // > If a subtraction results in a borrow into the high-order bit of the
        //   result, then CF is set; otherwise CF is cleared.
        // For now, just clear CF.
        self.cf = 0;
        self.af = 0;
        self.sf = (y < 0) as u8;
        self.zf = (y == 0) as u8;

        // TODO: audit
        self.pf = (y.count_ones() % 2 == 0) as u8;
        self.of = 0;
    }

    fn add_imm_unsigned(&mut self, dst: RegisterTag, src: u16) {
        // TODO set flags
        let value = src + self.load(dst);
        self.store(dst, value);
    }

    fn add_reg_unsigned(&mut self, dst: RegisterTag, src: RegisterTag) {
        // TODO set flags
        let value = self.load(src) + self.load(dst);
        self.store(dst, value);
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

    fn jump_gt_equal(&mut self, label: &str) {
        if (self.sf ^ self.of) == 0 {
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

    fn push_reg(&mut self, src: RegisterTag) {
        let src = self.load(src);
        self.push(src);
    }

    fn pop_reg(&mut self, dst: RegisterTag) {
        let value = self.pop();
        self.store(dst, value);
    }

    fn ret(&mut self, n: u16) {
        // Grab the ip from the top of the stack first, then clean up.
        self.ip = self.pop();

        for _ in 0..n {
            let _ = self.pop();
        }
    }

    fn call(&mut self, proc: &str) {
        self.push(self.ip);
        self.ip = *self.symbol_table.get(proc).unwrap();
    }

    fn sub_imm(&mut self, dst: RegisterTag, src: u16) {
        // TODO set flags
        let value = self.load(dst) - src;
        self.store(dst, value);
    }

    fn interrupt(&mut self, vector: u16) {
        self.interrupt_handler
            .handle(vector, self.ax.high(), self.ax.low(), self.dx.low());
    }

    fn halt(&mut self) {
        self.halt = true;
    }
}

#[derive(Debug, PartialEq)]
pub struct MachineState {
    pub ax: u16,
    pub bx: u16,
}

impl<H: Interrupt + Default> Vm<H> {
    pub fn new() -> Self {
        Vm {
            ax: FullViewRegister::new(),
            bx: FullViewRegister::new(),
            dx: FullViewRegister::new(),
            cf: 0,
            af: 0,
            sf: 0,
            zf: 0,
            pf: 0,
            of: 0,
            ip: 0,
            sp: None,
            bp: 0,
            symbol_table: SymbolTable::default(),
            data_table: DataTable::default(),
            stack: vec![0; STACK_SIZE as usize],
            stack_limit: STACK_SIZE,
            interrupt_handler: H::default(),
            halt: false,
        }
    }

    pub fn run(&mut self, program: Program) -> Result<MachineState, Box<dyn Error>> {
        let Program(symbols, data, instructions) = program;
        self.symbol_table = symbols;
        self.data_table = data;
        self.ip = *self.symbol_table.get(ENTRY_POINT).unwrap();

        while !self.halt {
            let ip = self.ip() as usize;
            let op = instructions.get(ip).unwrap();
            op.eval(self);
        }

        Ok(self.state())
    }

    pub fn ip(&mut self) -> u16 {
        let instruction_pointer = self.ip;
        self.ip += 1;
        instruction_pointer
    }

    pub fn dump(&self) {
        eprintln!("{:?}", self.state());
    }

    pub fn state(&self) -> MachineState {
        MachineState {
            ax: self.ax.full(),
            bx: self.bx.full(),
        }
    }

    //
    // `push` and `pop` follow the historical convention of growing downward and
    // upward respectively. This differs from standard `stack` conventions but
    // is expected in _nominal_ assembler programming.
    //

    fn push(&mut self, value: u16) {
        let limit = self.stack_limit - 1;
        let sp = match self.sp {
            Some(0) => panic!("stack overflow! -- {:?}", self.stack),
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

    fn load(&self, tag: RegisterTag) -> u16 {
        match tag {
            RegisterTag::Ax => self.ax.full(),
            RegisterTag::Ah => self.ax.high() as u16,
            RegisterTag::Al => self.ax.low() as u16,
            RegisterTag::Bx => self.bx.full(),
            RegisterTag::Bh => self.bx.high() as u16,
            RegisterTag::Bl => self.bx.low() as u16,
            RegisterTag::Dx => self.dx.full(),
            RegisterTag::Dh => self.dx.high() as u16,
            RegisterTag::Dl => self.dx.low() as u16,
            RegisterTag::Bp => self.bp,
            RegisterTag::Sp => self.sp.unwrap(),
        }
    }

    fn store(&mut self, tag: RegisterTag, value: u16) {
        match tag {
            RegisterTag::Ax => self.ax.set_full(value),
            RegisterTag::Ah => self.ax.set_high(value.try_into().unwrap()),
            RegisterTag::Al => self.ax.set_low(value.try_into().unwrap()),
            RegisterTag::Bx => self.bx.set_full(value),
            RegisterTag::Bh => self.bx.set_high(value.try_into().unwrap()),
            RegisterTag::Bl => self.bx.set_low(value.try_into().unwrap()),
            RegisterTag::Dx => self.dx.set_full(value),
            RegisterTag::Dh => self.dx.set_high(value.try_into().unwrap()),
            RegisterTag::Dl => self.dx.set_low(value.try_into().unwrap()),
            RegisterTag::Bp => self.bp = value,
            RegisterTag::Sp => self.sp = Some(value),
        }
    }
}

#[derive(PartialEq, Debug)]
pub enum Op {
    AddImmUnsigned(RegisterTag, u16),
    AddReg(RegisterTag, RegisterTag),
    Call(String),
    CmpImm(RegisterTag, u16),
    Int(u16),
    Je(String),
    Jge(String),
    Jmp(String),
    Jne(String),
    MovImm(RegisterTag, u16),
    MovMem(RegisterTag, RegisterTag, Option<(OffsetOp, u16)>),
    MovVar(RegisterTag, String),
    MovReg(RegisterTag, RegisterTag),
    Pop(RegisterTag),
    Push(RegisterTag),
    Ret(u16),
    SubImm(RegisterTag, u16),
    Halt, //< Implementation detail
}

impl Op {
    pub fn eval<T: AbstractMachine>(&self, machine: &mut T) {
        match self {
            Self::AddImmUnsigned(dst, src) => machine.add_imm_unsigned(*dst, *src),
            Self::AddReg(dst, src) => machine.add_reg_unsigned(*dst, *src),
            Self::Call(proc) => machine.call(proc),
            Self::CmpImm(dst, src) => machine.compare_imm(*dst, *src),
            Self::Int(interrupt) => machine.interrupt(*interrupt),
            Self::Je(label) => machine.jump_equal(label),
            Self::Jge(label) => machine.jump_gt_equal(label),
            Self::Jmp(label) => machine.unconditional_jump(label),
            Self::Jne(label) => machine.jump_not_equal(label),
            Self::MovImm(dst, src) => machine.update_imm(*dst, *src),
            Self::MovMem(dst, src, offset) => machine.update_reg_from_mem(*dst, *src, offset),
            Self::MovVar(dst, var) => machine.update_reg_from_var(*dst, var),
            Self::MovReg(dst, src) => machine.update_reg(*dst, *src),
            Self::Pop(dst) => machine.pop_reg(*dst),
            Self::Push(src) => machine.push_reg(*src),
            Self::Ret(n) => machine.ret(*n),
            Self::SubImm(dst, src) => machine.sub_imm(*dst, *src),
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
        assert_eq!(Some(Token::Comma), tokens.next());
        assert_eq!(Some(Token::UnsignedImm(42)), tokens.next());
        assert_eq!(None, tokens.next());
    }

    #[test]
    fn lex_ignore_comments() {
        let mut tokens = lex("mov ax, 42 ; don't care".chars().peekable()).into_iter();
        assert_eq!(Some(Token::Mov), tokens.next());
        assert_eq!(Some(Token::Reg(RegisterTag::Ax)), tokens.next());
        assert_eq!(Some(Token::Comma), tokens.next());
        assert_eq!(Some(Token::UnsignedImm(42)), tokens.next());
        assert_eq!(None, tokens.next());
    }

    #[test]
    fn simple_parse() {
        let tokens = lex("main:\nmov ax, 42\nend main".chars().peekable()).into_iter();
        let mut ops = Parser::new(tokens.into_iter().peekable())
            .run()
            .2
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
            Token::Comma,
            Token::Reg(RegisterTag::Bx),
            Token::Label("Foo".to_owned()),
            Token::Add, // Op 1
            Token::Reg(RegisterTag::Ax),
            Token::Comma,
            Token::Reg(RegisterTag::Ax),
            Token::End,
            Token::Iden(String::from("main")),
        ];
        let Program(symbols, _, _) = Parser::new(tokens.into_iter().peekable()).run();
        assert_eq!(symbols.get("Foo"), Some(&(1)));
    }

    #[test]
    fn full_view_register() {
        let mut fvr = FullViewRegister::new();
        fvr.set_high(0x12);
        assert_eq!(0x1200, fvr.full());

        fvr.set_low(0xAB);
        assert_eq!(0x12AB, fvr.full());

        fvr.set_high(0xAA);
        assert_eq!(0xAA, fvr.high());

        assert_eq!(0xAAAB, fvr.full());
    }
}
