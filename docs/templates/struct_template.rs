// Verus Struct Template
// Reference: https://verus-lang.github.io/verus/guide/datatypes_struct.html

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    // Basic struct definition with int types (Verus native)
    pub struct ExampleStruct {
        pub field1: int,
        pub field2: int,
    }

    // Struct with spec functions for validation
    impl ExampleStruct {
        // Specification function for struct validation
        spec fn is_valid(&self) -> bool {
            self.field1 >= 0 && self.field2 >= 0
        }

        // Specification function for calculations
        spec fn sum(&self) -> int {
            self.field1 + self.field2
        }
    }

    // Example usage in exec function
    pub exec fn create_example() -> (result: ExampleStruct)
        ensures
            result.is_valid(),
            result.sum() >= 0
    {
        ExampleStruct { field1: 5, field2: 3 }
    }

    // Example with struct operations
    pub exec fn manipulate_struct(s: ExampleStruct) -> (result: ExampleStruct)
        requires
            s.is_valid()
        ensures
            result.is_valid(),
            result.sum() == s.sum() + 1
    {
        ExampleStruct {
            field1: s.field1,
            field2: s.field2 + 1
        }
    }
}
