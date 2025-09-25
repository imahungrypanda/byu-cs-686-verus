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
      let s_low: Seq<int> = s.subrange(0, low);
      let s_high: Seq<int> = s.subrange(high, s.len() as int);
      assert(s =~= s_low + s_high);
    } else {
      let mid: int = low + (high - low) / 2;

      if (x > s[mid]) {
        binary_search_core_ensures(x, s, mid + 1, high)
      } else {
        binary_search_core_ensures(x, s, low, mid)
      }
    }
  }

  proof fn binary_search_ensures(x: int, s: Seq<int>)
    requires
      is_sorted(s),
    ensures
      match binary_search_spec(x, s) {
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
  {
    if 0 == s.len() {
    } else if x < s.first() {
    } else if x > s.last() {
    } else {
      binary_search_core_ensures(x, s, 0, s.len() - 1)
    }
  }

  proof fn test() {
    let s: Seq<int> = seq![1, 2, 3, 4, 4,  5, 6];
    let mut x: int = 3;
    let mut expected: Option<int> = Some(2);

    let mut answer: Option<int> = binary_search_spec(x, s);
    assert(answer == expected) by {
      binary_search_ensures(x, s);
    };

    x = -4;
    expected = None::<int>;
    answer = binary_search_spec(x, s);
    assert(answer == expected);
  }

  spec fn seq_usize_to_int(x: Seq<usize>) -> Seq<int>
  {
    x.map_values(|x: usize| x as int)
  }

  spec fn option_usize_to_int(o: Option<usize>) -> Option<int> {
    match(o) {
      Some(i) => Some(i as int),
      None::<usize> => None::<int>,
    }
  }

  exec fn binary_search_core(x: usize, s: Vec<usize>, low: usize, high: usize) -> (result: Option<usize>)
    requires
      is_sorted(seq_usize_to_int(s@)),
      0 <= low <= high < s.len(),
      elements_s_lt_x(x as int, seq_usize_to_int(s@).subrange(0, low as int)),
      elements_s_ge_x(x as int, seq_usize_to_int(s@).subrange(high as int, s.len() as int)),
    ensures
      binary_search_core_spec(x as int, seq_usize_to_int(s@), low as int, high as int) == option_usize_to_int(result)
  {
    let mut ll: usize = low;
    let mut hh: usize = high;

    while ll != hh
      invariant
        is_sorted(seq_usize_to_int(s@)),
        0 <= low <= ll <= hh <= high <= s.len(),
        elements_s_lt_x(x as int, seq_usize_to_int(s@).subrange(0, ll as int)),
        elements_s_ge_x(x as int, seq_usize_to_int(s@).subrange(hh as int, s.len() as int)),
      decreases
        hh - ll
    {
      let mut mid: usize = ll + (hh - ll) / 2;

      if x > s[mid] {
        ll = mid + 1;
        let ghost s_low: Seq<int> = seq_usize_to_int(s@).subrange(0, ll as int);
        assert(s_low.last() < x as int);
      } else {
        hh = mid;

        let ghost s_high: Seq<int> = seq_usize_to_int(s@).subrange(hh as int, s@.len() as int);
        assert(s_high.first() >= x as int);
      }
    }

    let ghost s_all: Seq<int> = seq_usize_to_int(s@);
    assert(binary_search_core_spec(x as int, s_all, low as int, high as int)
        == binary_search_core_spec(x as int, s_all, ll as int, hh as int)) by {
        binary_search_core_ensures(x as int, s_all, low as int, high as int);
        binary_search_core_ensures(x as int, s_all, ll as int, hh as int);
    };

    let answer: Option<usize> = if x == s[ll] {
      Some(ll)
    } else {
      None::<usize>
    };

    answer
  }

  pub fn run_examples() {

  }






}
