pub trait Handler {
    fn handle(&self, vector: u16, ah: u8, al: u8);
}
