// check-pass



fn main (){
    let mut x = 5;
    let raw = &mut x as *mut i32;
    let one = 1024  ;
    
    let address = *raw - one;
    //let points_at = unsafe { *raw };
    println!("raw points at {:?}", raw);
    println!("one points at {:?}", one);

    println!("compare {}", address);

}



