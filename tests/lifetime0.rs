// check-pass

fn main (){
    let mut v = vec![10, 11];
    v.push(12);
    let vptr = &mut v[1];
    *vptr = 23;
    println! ("{:?}", v);
    return ();
}

