// Verus Advanced Loop Template with Invariants and Break
// Reference: https://verus-lang.github.io/verus/guide/recursion_loops.html#loops-and-invariants

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    // Template for while loops with invariants
    exec fn loop_with_invariant(a: &Vec<u64>) -> (sum: u64)
        ensures
            sum == a.len() as u64 * (a.len() as u64 + 1) / 2,  // Example postcondition
    {
        let mut i: usize = 0;
        let mut acc: u64 = 0;

        while i < a.len()
            invariant
                i <= a.len(),
                acc == i as u64 * (i as u64 + 1) / 2,  // Invariant property
                forall |j: int| 0 <= j < i as int ==> a[j] >= 0,  // Array property
        {
            acc = acc + a[i];
            i = i + 1;
        }

        acc
    }

    // Template for loops with break statements - using separate functions for simplicity
    exec fn find_target_index(a: &Vec<u64>, target: u64) -> (index: usize)
        ensures
            index <= a.len(),
            (exists |i: int| 0 <= i < a.len() as int && a[i] == target) ==>
                (index < a.len() && a[index] == target),
            !(exists |i: int| 0 <= i < a.len() as int && a[i] == target) ==> index == a.len(),
    {
        let mut i: usize = 0;

        while i < a.len()
            invariant
                i <= a.len(),
                forall |j: int| 0 <= j < i as int ==> a[j] != target,  // Haven't found target yet
        {
            if a[i] == target {
                return i;
            }
            i = i + 1;
        }

        i
    }

    exec fn target_exists(a: &Vec<u64>, target: u64) -> (found: bool)
        ensures
            found == (exists |i: int| 0 <= i < a.len() as int && a[i] == target),
    {
        let index = find_target_index(a, target);
        index < a.len()
    }

    // Template for nested loops with complex invariants
    exec fn nested_loops(matrix: &Vec<Vec<u64>>) -> (sum: u64)
        requires
            forall |i: int| 0 <= i < matrix.len() as int ==> matrix[i].len() > 0,
        ensures
            sum == sum_matrix_spec(matrix),
    {
        let mut i: usize = 0;
        let mut total: u64 = 0;

        while i < matrix.len()
            invariant
                i <= matrix.len(),
                total == sum_rows_up_to(matrix, i as int),
        {
            let mut j: usize = 0;
            let mut row_sum: u64 = 0;

            while j < matrix[i].len()
                invariant
                    j <= matrix[i].len(),
                    row_sum == sum_elements_up_to(matrix[i], j as int),
            {
                row_sum = row_sum + matrix[i][j];
                j = j + 1;
            }

            total = total + row_sum;
            i = i + 1;
        }

        total
    }

    // Helper spec functions for verification
    spec fn sum_matrix_spec(matrix: &Vec<Vec<u64>>) -> u64
        decreases matrix.len() as int,
    {
        if matrix.len() == 0 {
            0
        } else {
            sum_vector_spec(&matrix[0]) + sum_matrix_spec(&matrix[1..])
        }
    }

    spec fn sum_vector_spec(v: &Vec<u64>) -> u64
        decreases v.len() as int,
    {
        if v.len() == 0 {
            0
        } else {
            v[0] + sum_vector_spec(&v[1..])
        }
    }

    spec fn sum_rows_up_to(matrix: &Vec<Vec<u64>>, i: int) -> u64
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            sum_vector_spec(&matrix[(i - 1) as usize]) + sum_rows_up_to(matrix, i - 1)
        }
    }

    spec fn sum_elements_up_to(v: &Vec<u64>, j: int) -> u64
        decreases j,
    {
        if j <= 0 {
            0
        } else {
            v[(j - 1) as usize] + sum_elements_up_to(v, j - 1)
        }
    }
}
