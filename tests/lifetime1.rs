// check-pass

fn main (){
    unsafe {
        let mut v = vec![10, 11];
        let vptr = &mut v[1]; // Points *into* v.
    //println! ("{:?}", v);
        v.push(12); // May reallocate the backing store of v. 
        println!("v[1] = {}", *vptr); // Compiler error!
        v.push(12);
    }
    return ();
}
