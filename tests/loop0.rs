// check-pass

fn main (){
    let mut v = vec! [1, 2, 3];
    for i in &v {
        println! ("{}", i);
        v.push(42);
    }
}