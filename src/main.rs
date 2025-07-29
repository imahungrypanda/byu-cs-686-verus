use vstd::prelude::*;

verus! {

    spec fn min(x: int, y: int) -> int {
        if x <= y {
            x
        } else {
            y
        }
    }

    fn foo() {
        assert(min(10, 20) == 10);
        assert(min(-10, -20) == -20);
        assert(forall|i: int, j: int| min(i, j) <= i && min(i, j) <= j);
        assert(forall|i: int, j: int| min(i, j) == i || min(i, j) == j);
        assert(forall|i: int, j: int| min(i, j) == min(j, i));
        // assert(forall|i: int, j: int| min(i, j) == min(i, i));
    }

    // Verified, but executable
    pub fn fn_min(x: i32, y: i32) -> i32 {
        if x <= y { x } else { y }
    }

} // verus!

fn main() {
    println!("Hello world! And goodbye.");
    foo();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_min_exec() {
        assert_eq!(fn_min(10, 20), 10);
        assert_eq!(fn_min(5, -5), -5);
    }
}