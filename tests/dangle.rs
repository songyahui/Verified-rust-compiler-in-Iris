// check-pass


fn main() {
    let reference_to_nothing = 
        unsafe{dangle()};
}

unsafe fn dangle() -> &String {
    let s = String::from("hello");

    &s
}
