pub trait Handler {
    fn handle(&self, vector: &str, ah: u8, al: u8);
}
