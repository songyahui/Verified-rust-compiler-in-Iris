// check-pass

use std::future::join;

fn main (){
    let mut x = 1;
    let thread1 = println!("Thread 1: {}", &x);
    let thread2 = println!("Thread 2: {}", &x);
    join!(thread1, thread2);
    x = 2; 
    return ();
}