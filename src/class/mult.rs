use vstd::prelude::*;

verus! {

  spec fn mult_spec(n: nat, m: nat) -> nat
    decreases n,
  {
      if n == 0 {
        0
      } else {
        let n0: nat = (n - 1) as nat;
        mult_spec(n0, m) + m
      }
  }

  proof fn lemma_mult_spec(n: nat, m: nat)
    by (nonlinear_arith)
    ensures
      mult_spec(n, m) == n * m,
    decreases n
  {
    if n == 0 {
    } else {
      let n0: nat = (n - 1) as nat;
      lemma_mult_spec(n0, m);
    }
  }

  exec fn mult(n: usize, m: usize) -> (result: usize)
    requires
      n * m <= usize::MAX,
    ensures
      result == mult_spec(n as nat, m as nat),
    decreases n
  {
    let mut i: usize = n;
    let mut result: usize = 0;

    while i > 0
      invariant
        n * m <= usize::MAX,
        n * m == result + i * m,
      decreases i,
    {
      assert(result + m <= usize::MAX) by {
        broadcast use vstd::arithmetic::mul::group_mul_properties;
      }

      result = result + m;
      i = i - 1;

      assert(n * m == result + i * m) by {
        broadcast use vstd::arithmetic::mul::group_mul_is_commutative_and_distributive;
      }
    }

    proof {
        lemma_mult_spec(n as nat, m as nat);
    }

    return result
  }

  pub fn run_examples() {
      assert(20 == mult_spec(4, 5)) by {
        reveal_with_fuel(mult_spec, 5);
      };
  }

} // verus!


// A sound model of the actual code
