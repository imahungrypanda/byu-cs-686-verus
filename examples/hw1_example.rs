use vstd::prelude::*;

verus! {

fn octuple(x1: i8) -> i8
    requires
        -16 <= x1,
        x1 < 16,
{
    let x2 = x1 + x1;
    let x4 = x2 + x2;
    x4 + x4
}

fn main() {
    let n = octuple(100);
    assert(n == 80);
}

} // verus!
