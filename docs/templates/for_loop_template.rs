// Verus For Loop Template
// Reference: https://verus-lang.github.io/verus/guide/recursion_loops.html#for-loops

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    // Template for verified for loops
    exec fn for_loop_example(a: &Vec<u64>) -> (sum: u64)
        ensures
            sum == sum_vector_spec(a),
    {
        let mut sum: u64 = 0;

        for i in 0..a.len()
            invariant
                sum == sum_up_to_spec(a, i as int),
        {
            sum = sum + a[i];
        }

        sum
    }

    // Template for for loop with early break - split into separate functions
    exec fn find_target_index_for_loop(a: &Vec<u64>, target: u64) -> (index: usize)
        ensures
            index <= a.len(),
            (exists |i: int| 0 <= i < a.len() as int && a[i] == target) ==>
                (index < a.len() && a[index] == target),
            !(exists |i: int| 0 <= i < a.len() as int && a[i] == target) ==> index == a.len(),
    {
        for i in 0..a.len()
            invariant
                forall |j: int| 0 <= j < i as int ==> a[j] != target,
        {
            if a[i] == target {
                return i;
            }
        }

        a.len()
    }

    exec fn target_exists_for_loop(a: &Vec<u64>, target: u64) -> (found: bool)
        ensures
            found == (exists |i: int| 0 <= i < a.len() as int && a[i] == target),
    {
        let index = find_target_index_for_loop(a, target);
        index < a.len()
    }

    // Template for for loop with nested iterations
    exec fn for_loop_nested(matrix: &Vec<Vec<u64>>) -> (max_element: u64)
        requires
            matrix.len() > 0,
            forall |i: int| 0 <= i < matrix.len() as int ==> matrix[i].len() > 0,
        ensures
            exists |i: int, j: int|
                0 <= i < matrix.len() as int &&
                0 <= j < matrix[i as usize].len() as int &&
                matrix[i as usize][j as usize] == max_element,
            forall |i: int, j: int|
                0 <= i < matrix.len() as int &&
                0 <= j < matrix[i as usize].len() as int ==>
                matrix[i as usize][j as usize] <= max_element,
    {
        let mut max_element: u64 = 0;
        let mut first_element: bool = true;

        for i in 0..matrix.len() {
            for j in 0..matrix[i].len()
                invariant
                    forall |k: int, l: int|
                        0 <= k < i as int ||
                        (k == i as int && 0 <= l < j as int) ==>
                        matrix[k as usize][l as usize] <= max_element,
                    first_element == (i == 0 && j == 0),
            {
                if first_element || matrix[i][j] > max_element {
                    max_element = matrix[i][j];
                    first_element = false;
                }
            }
        }

        max_element
    }

    // Template for for loop with range bounds
    exec fn for_loop_range(start: usize, end: usize) -> (sum: u64)
        requires
            start <= end,
            end - start <= 1000,  // Prevent overflow
        ensures
            sum == sum_range_spec(start, end),
    {
        let mut sum: u64 = 0;

        for i in start..end
            invariant
                sum == sum_range_spec(start, i),
        {
            sum = sum + i as u64;
        }

        sum
    }

    // Helper spec functions for verification
    spec fn sum_vector_spec(a: &Vec<u64>) -> u64
        decreases a.len() as int,
    {
        if a.len() == 0 {
            0
        } else {
            a[0] + sum_vector_spec(&a[1..])
        }
    }

    spec fn sum_up_to_spec(a: &Vec<u64>, i: int) -> u64
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            a[(i - 1) as usize] + sum_up_to_spec(a, i - 1)
        }
    }

    spec fn sum_range_spec(start: usize, end: usize) -> u64
        decreases (end - start) as int,
    {
        if start >= end {
            0
        } else {
            start as u64 + sum_range_spec(start + 1, end)
        }
    }
}
