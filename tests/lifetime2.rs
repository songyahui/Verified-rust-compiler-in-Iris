// check-pass

fn main (){
    let mut v = vec![10, 11];
    let v2= mut v;
    let vptr = &mut v[1];
    println!("v[1] = {}", *vptr);
    v.push(12); // May reallocate the backing store of v. 
     // Compiler error!
    return ();
 
}

