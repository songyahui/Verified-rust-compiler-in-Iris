// check-pass

// unsafe, but should NOT be semantically well-typed
use std::slice;

fn split_at_mut(slice: &mut [i32], mid: usize) -> (&mut [i32], &mut [i32]) {
    let len = slice.len();
    let ptr = slice.as_mut_ptr();

    assert!(mid <= len);

    unsafe {
        (
            // <!borrowed (ptr, 6)>
            /* !borrowed (ptr, 6) |= !borrowed (ptr, 2) : Valid! */
            slice::from_raw_parts_mut(ptr, mid),
            // <!borrowed (ptr, 6) /\ borrowed  (ptr, 2)>
            // <!borrowed (ptr+2, 4)>
            /* !borrowed (ptr+2, 4) |= !borrowed (ptr+2-1, 4) : Invalid X */
            slice::from_raw_parts_mut(ptr.add(mid-1), len - mid),
        )
    }
}

fn main (){
    let mut v = vec![1, 2, 3, 4, 5, 6];

    let r = &mut v[..];

    let (_, _) = split_at_mut(r, 3);
    return ();

}

