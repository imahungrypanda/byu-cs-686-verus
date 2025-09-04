# HW0 Runbook (Exact Steps)

Follow these to produce the required screenshots per homework/hw0-verus-install.md.

## Step 2: getting_started.rs (verifies)
1) Save file: `examples/getting_started.rs` (below).
2) Run: `verus examples/getting_started.rs`
3) Screenshot terminal showing verification success.

## Step 2 (modified): getting_started.rs (fails)
1) Save file: `examples/getting_started_fail.rs` (below).
2) Run: `verus examples/getting_started_fail.rs`
3) Screenshot terminal showing verification failure.

## Step 3
Follow the guide’s step 3; run the indicated command and screenshot the result.

## VS Code verus-analyzer failure in main.rs
1) Open `src/main.rs` (ensure it has a failing assertion).
2) Take a screenshot with the error squiggles from verus-analyzer visible.

---

## Files

### examples/getting_started.rs
A minimal file that should verify.

```rust
#![allow(unused_imports)]
use vstd::prelude::*;
verus! {
    pub exec fn inc(x: u64) -> (y: u64)
        ensures y == x + 1
    {
        x + 1
    }
}
```

### examples/getting_started_fail.rs
A variant that should fail verification.

```rust
#![allow(unused_imports)]
use vstd::prelude::*;
verus! {
    pub exec fn inc_bad(x: u64) -> (y: u64)
        ensures y == x + 2
    {
        // Intentionally wrong implementation
        x + 1
    }
}
```
