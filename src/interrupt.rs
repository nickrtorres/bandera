use std::process::exit;

const DOS_INTERRUPT_VECTOR: u16 = 0x21;

pub trait Interrupt {
    fn handle(&self, vector: u16, ah: u8, al: u8);
}

pub struct Dos {}

impl Default for Dos {
    fn default() -> Self {
        Dos {}
    }
}

impl Interrupt for Dos {
    fn handle(&self, vector: u16, ah: u8, al: u8) {
        if vector != DOS_INTERRUPT_VECTOR {
            return;
        }

        match ah {
            0x4C => exit(al as i32),
            v => todo!("Unhandled interrupt => 0x{:x}", v),
        }
    }
}
