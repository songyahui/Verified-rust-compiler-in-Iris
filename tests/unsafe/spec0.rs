// check-pass
use std::slice;

/*
pub const unsafe fn add(self, count: usize) -> Self
    where
        T: Sized,
// requires true
// ensures self + count
*/


/*
pub unsafe fn from_raw_parts_mut<'a, T>(data: *mut T, len: usize) -> &'a mut [T] 
// requires !borrowed (data, len)
// ensures  borrowed  (data, len)
{...}
*/

fn split_at_mut(slice: & [i32], mid: usize) -> (& [i32], & [i32]) 
{
    let len = slice.len();
    let ptr = slice.as_ptr();
    println!("length {:?}", slice);//6
    assert!(mid <= len);
    //slice::split_at(mid)


    unsafe {
        (
            // <!borrowed (ptr, 6)>
            /* !borrowed (ptr, 6) |= !borrowed (ptr, 2) : Valid! */
            slice::from_raw_parts(ptr, mid),
            // <!borrowed (ptr, 6) /\ borrowed  (ptr, 2)>
            // <!borrowed (ptr+2, 4)>
            /* !borrowed (ptr+2, 4) |= !borrowed (ptr+2, 4) : Valid */
            slice::from_raw_parts(ptr.add(mid), len - mid),
            // <!borrowed (ptr+2, 4) /\ borrowed  (ptr+2, 4)>
            // <borrow (ptr, 6)> 

        )
    }
}

fn main (){
    let mut v = vec![1, 2, 3, 4, 5, 6];
    //v.swap (1, 1);
    let r = &mut v[..];

    let (a, b) = split_at_mut(r, 2);
    println!("length {}, {}", a.len(), b.len());
    return ();

}

