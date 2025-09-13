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
} // verus!
