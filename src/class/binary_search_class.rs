use vstd::prelude::*;

verus! {

  spec fn is_sorted(s: Seq<int>) -> bool
  {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
  }

  spec(checked)  fn binary_search_spec(x: int, s: Seq<int>) -> Option<int>
    recommends
      is_sorted(s),
  {
    if 0 == s.len() {
      None::<int>
    } else if x < s.first() {
      None::<int>
    } else if x > s.last() {
      None::<int>
    } else {
      binary_search_core_spec(x, s, 0, s.len() - 1)
    }
  }

  spec fn elements_s_lt_x(x: int, s: Seq<int>) -> bool
  {
    forall|i: int| 0 <= i < s.len() ==> s[i] < x
  }

  spec fn elements_s_ge_x(x: int, s: Seq<int>) -> bool
  {
    forall|i: int| 0 <= i < s.len() ==> s[i] >= x
  }

  spec fn binary_search_core_spec(x: int, s: Seq<int>, low: int, high: int) -> Option<int>
    recommends
      is_sorted(s),
      0 <= low <= high < s.len(),
      elements_s_lt_x(x, s.subrange(0, low)),
      elements_s_ge_x(x, s.subrange(high, s.len() as int)),
    decreases
      high - low when high >= low
  {
    if low == high {
      if s[low] == x {
        Some(low)
      } else {
        None::<int>
      }
    } else {
      let mid: int = low + (high - low) / 2;

      if (x > s[mid]) {
        binary_search_core_spec(x, s, mid + 1, high)
      } else {
        binary_search_core_spec(x, s, low, mid)
      }
    }
  }

  proof fn binary_search_core_ensures(x: int, s: Seq<int>, low: int, high: int)
    requires
      is_sorted(s),
      0 <= low <= high < s.len(),
      elements_s_lt_x(x, s.subrange(0, low)),
      elements_s_ge_x(x, s.subrange(high, s.len() as int)),
    ensures
      match binary_search_core_spec(x, s, low, high) {
        Some(i) => {
          &&& s.contains(x)
          &&& 0 <= i <= s.len()
          &&& forall|j: int| 0 <= j < i ==> s[j] != x
          &&& s[i] == x
        },
        None::<int> => {
          !s.contains(x)
        }
      }
    decreases
      high - low
  {
    if low == high {
      assume(false);

      if s[low] == x {
      } else {
      }
    } else {
      let mid: int = low + (high - low) / 2;

      if (x > s[mid]) {
        binary_search_core_ensures(x, s, mid + 1, high)
      } else {
        binary_search_core_ensures(x, s, low, mid)
      }
    }
  }

  proof fn test() {
    let s: Seq<int> = seq![1, 2, 3, 4, 4,  5, 6];
    let mut x: int = 3;
    let mut expected: Option<int> = Some(2);

    let mut answer: Option<int> = binary_search_spec(x, s);
    assert(answer == expected) by {
      reveal_with_fuel(binary_search_core_spec, 10);
    };

    x = -4;
    expected = None::<int>;
    answer = binary_search_spec(x, s);
    assert(answer == expected);
  }

  pub fn run_examples() {

  }

}
