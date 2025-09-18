use vstd::prelude::*;

verus! {

  spec fn is_sorted(s: Seq<int>) -> bool
  {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
  }

  spec fn binary_search_core(x: int, s: Seq<int>, low: int, high: int) -> Option<int>
    recommends
      s.len() > 0,
      is_sorted(s),
    decreases high - low
  {
    if low > high {
      None::<int>
    } else {
      let mid: int = (low + high) / 2;
      if s[mid] == x {
        Some(mid)
      } else if s[mid] < x {
        binary_search_core(x, s, mid + 1, high)
      } else {
        binary_search_core(x, s, low, mid - 1)
      }
    }
  }

  spec fn binary_search_spec(x: int, s: Seq<int>) -> Option<int>
    recommends
      is_sorted(s),
  {
    if 0 == s.len() {
      None::<int>
    } else {
      binary_search_core(x, s, 0, s.len() - 1)
    }
  }

  pub fn run_examples() {

  }

}
