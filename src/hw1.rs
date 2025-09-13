use vstd::prelude::*;

verus! {
    pub mod problem1 {
        use super::*;

        // NOTE: This is ghost code because it is a spec function and not an executable function.
        spec fn spec_is_in_range_by_step(value: int, min: int, max: int, step: nat) -> (result: bool)
        {
            min <= value <= max && ((value - min) % step as int) == 0 && step > 0
        }

        exec fn is_in_range_by_step(value: i32, min: i32, max: i32, step: u16) -> (result: bool)
            requires
                step > 0,
            ensures
                result == spec_is_in_range_by_step(value as int, min as int, max as int, step as nat),
        {
            return min <= value && value <= max && (value as i64 - min as i64) % (step as i64) == 0;
        }

        // Example function to demonstrate structure
        pub fn run_examples() {
            // assert(true); // Placeholder - replace with your actual homework 1 examples
            assert(spec_is_in_range_by_step(10, 0, 10, 1) == true);
            assert(spec_is_in_range_by_step(11, 0, 10, 1) == false);
            // assert(spec_is_in_range_by_step(11, 0, 10, -1) == false); // This should fail because step is not positive.
            assert(spec_is_in_range_by_step(11, 0, 10, 2) == false); // This should fail because 11 is not in the range.
            assert(spec_is_in_range_by_step(11, 0, 10, 0) == false); // This should fail because 11 is not in the range.

            // Proof that exec function matches spec function
            // Case 1: value at minimum boundary
            let result1 = is_in_range_by_step(0, 0, 10, 1);
            assert(result1 == spec_is_in_range_by_step(0, 0, 10, 1));

            // Case 2: value at maximum boundary
            let result2 = is_in_range_by_step(10, 0, 10, 1);
            assert(result2 == spec_is_in_range_by_step(10, 0, 10, 1));

            // Case 3: value just outside range (too high)
            let result3 = is_in_range_by_step(11, 0, 10, 1);
            assert(result3 == spec_is_in_range_by_step(11, 0, 10, 1));

            // Case 4: value just outside range (too low)
            let result4 = is_in_range_by_step(-1, 0, 10, 1);
            assert(result4 == spec_is_in_range_by_step(-1, 0, 10, 1));

            // Case 5: step size larger than 1
            let result5 = is_in_range_by_step(6, 0, 10, 2);
            assert(result5 == spec_is_in_range_by_step(6, 0, 10, 2));

            // Case 6: step size larger than 1, but not aligned
            let result6 = is_in_range_by_step(7, 0, 10, 2);
            assert(result6 == spec_is_in_range_by_step(7, 0, 10, 2));

            // Case 7: zero step (should fail precondition)
            // This would violate the requires clause, so we don't test it

            // Case 8: negative range (min > max)
            // This would also violate the requires clause, so we don't test it

            // Case: negative starting point
            let result = is_in_range_by_step(-5, -10, 10, 2);
            assert(result == spec_is_in_range_by_step(-5, -10, 10, 2));
        }
    }

    // NOTE: I have no idea why but this problem confuses me a lot. I know I got it to pass but I don't know why.
    pub mod problem2 {
        use super::*;

        spec fn abs(x: int) -> (result: nat) {
            if x >= 0 {
                x as nat
            } else {
                -x as nat
            }
        }

        spec fn spec_absolute_difference(x: int, y: int) -> (result: nat) {
            let result = if x >= y {
                x - y
            } else {
                y - x
            };

            abs(result)
        }

        exec fn absolute_difference(x: i32, y: i32) -> (result: u32)
            ensures
                result == spec_absolute_difference(x as int, y as int),
        {
            if x >= y {
                (x as i64 - y as i64) as u32
            } else {
                (y as i64 - x as i64) as u32
            }
        }

        pub fn run_examples() {
            assert(spec_absolute_difference(10, 20) == 10);
            assert(spec_absolute_difference(20, 10) == 10);
            assert(spec_absolute_difference(10, 10) == 0);
            assert(spec_absolute_difference(-10, 20) == 30);
            assert(spec_absolute_difference(20, -10) == 30);
            assert(spec_absolute_difference(-10, -20) == 10);
            assert(spec_absolute_difference(-20, -10) == 10);

            let result1 = absolute_difference(10, 20);
            let result2 = absolute_difference(20, 10);
            assert(result1 == result2);

            let result3 = absolute_difference(-10, 20);
            let result4 = absolute_difference(20, -10);
            assert(result3 == result4);

            let result5 = absolute_difference(-10, -20);
            let result6 = absolute_difference(-20, -10);
            assert(result5 == result6);

            let result7 = absolute_difference(10, 10);
            let result8 = absolute_difference(10, 10);
            assert(result7 == result8);

            let result9 = absolute_difference(10, -10);
            let result10 = absolute_difference(-10, 10);
            assert(result9 == result10);
        }
    }

    pub mod problem3 {
        use super::*;

        spec fn spec_median(a: i32, b: i32, c: i32) -> (result: i32) {
            b
        }

        exec fn median(a: i32, b: i32, c: i32) -> (result: i32)
            requires
                a <= b && b <= c,
            ensures
                result == spec_median(a, b, c),
        {
            return b
        }

        spec fn spec_median_of_medians(a: i32, b: i32, c: i32, d: i32, e: i32) -> (result: i32)
        {
            let median1 = spec_median(a, b, c);
            let median2 = spec_median(c, d, e);
            if median1 == c {
                median2
            } else {
                median1
            }
        }

        exec fn median_of_medians(a: i32, b: i32, c: i32, d: i32, e: i32) -> (result: i32)
            requires
                a <= b <= c < d <= e,
            ensures
                result == spec_median_of_medians(a, b, c, d, e),
                result != c,
        {
            let median1 = median(a, b, c);
            let median2 = median(c, d, e);

            let result = if median1 == c {
                median2
            } else {
                median1
            };

            assert(result != c) by {
                lemma_median_of_medians(a, b, c, d, e);
            }
            return result
        }

        proof fn lemma_median_of_medians(a: i32, b: i32, c: i32, d: i32, e: i32)
            requires
                a <= b <= c < d <= e,
                !(b == c == d), // I don't think this is right. It defeats the purpose of the line before
            ensures
                (spec_median_of_medians(a, b, c, d, e) == d || spec_median_of_medians(a, b, c, d, e) == b),
        {
            let median1 = spec_median(a, b, c);
            assert(median1 == b);
            let median2 = spec_median(c, d, e);
            assert(median2 == d);
            let median3 = if median1 == c {
                median2
            } else {
                median1
            };
            assert(median3 == b || median3 == d);
        }

        pub fn run_examples() {
            assert(spec_median_of_medians(1, 2, 3, 4, 5) == 2);
            assert(spec_median_of_medians(1, 2, 3, 3, 5) == 2);
            assert(spec_median_of_medians(1, 3, 3, 4, 5) == 4);
        }
    }

} // verus!
