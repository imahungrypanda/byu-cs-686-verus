use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn print_two_digit_number(i: i8)
    requires
        -99 <= i < 100,
{
    println!("The answer is {}", i);
}

fn octuple(x1: i8) -> (x8: i8)
    requires
        -16 <= x1 < 16,
    ensures
        x8 == 8 * x1,
{
    let x2 = x1 + x1;
    let x4 = x2 + x2;
    x4 + x4
}

fn test_sum(x: u8, y: u8) -> (u16) {
    let sum1: u16 = x as u16 + y as u16;
    return sum1;
}

fn test_sum1(x: u8, y: u8) -> (u8)
    requires
        x + y < 256,
{
    let sum1: u8 = x + y;
    return sum1;
}


spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

// Example function to demonstrate structure
pub fn run_examples() {
    // Add your homework 1 examples here
    // Use assert statements instead of println! for Verus
    assert(true); // Placeholder - replace with your actual homework 1 examples
    let n = octuple(10);
    assert(n == 80);
    // assume(false);
    // assert(2 + 2 == 5);

    print_two_digit_number(n);

    assert(min(10, 20) == 10); // succeeds
    assert(min(100, 200) == 100); // succeeds
}


mod m1 {
    use verus_builtin::*;

    pub closed spec fn min(x: int, y: int) -> int {
        if x <= y {
            x
        } else {
            y
        }
    }

    pub proof fn lemma_min(x: int, y: int)
        ensures
            min(x,y) <= x && min(x,y) <= y,
    {}
}

mod m2 {
    use verus_builtin::*;
    use super::m1::*;

    fn test() {
        assert(min(10, 20) == min(10, 20)); // succeeds
        // assert(min(10, 20) == 10); // FAILS
        proof {
            lemma_min(10,20);
        }
        assert(min(10, 20) <= 10); // succeeds
    }
}

} // verus!
