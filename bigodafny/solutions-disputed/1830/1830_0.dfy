// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-12
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     `st` and `ed` are declared `seq(26, _ => 0)` and only ever
//     indexed/updated at positions 0..25 (one per uppercase letter), so
//     `SortInts(st)` and `SortInts(ed)` cost O(1) regardless of n; the
//     sole n-scaling work is the `while idx < n` loop doing O(1) per
//     character, making the method O(n) rather than the labelled O(nlogn),
//     and Python's fixed-size `st.sort()`/`ed.sort()` show the same
//     pattern.
//
//   how this label could be wrong, and what to check:
//     The label likely assumes `SortInts(st)`/`SortInts(ed)` sorts an
//     n-length array. Check the declarations `var st := seq(26, _ => 0)`
//     and `var ed := seq(26, _ => 0)`: both stay fixed at length 26 (one
//     per letter) regardless of the guest count n, so the sort is O(26 log
//     26)=O(1); the only loop that scales with n is the first `while idx <
//     n` pass over the guest string, so the true cost is O(n), and
//     Python's `st.sort()`/`ed.sort()` sort the same fixed 26-element
//     lists.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 62, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 3,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": true, "set_build_in_loop":
//     false, "sorts": ["SortInts"], "uses_map": false, "uses_multiset":
//     false, "uses_set": false}
// --------------------------------------------------------------------

// 834_B. The Festive Evening  (problem 1830, solution 1830_0)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// n, k = map(int, input().split())
// a = list(input())
// st = [0] * 26
// ed = [0] * 26
// for i in range(n):
// 	if st[ord(a[i])-65] == 0:
// 		st[ord(a[i])-65] = i + 1
// 	else:
// 		ed[ord(a[i])-65] = i + 1
// for i in range(26):
// 	if st[i] != 0 and ed[i] == 0:
// 		ed[i] = st[i]
// n = 52
// i = 0
// j = 0
// maxi = -1 * sys.maxsize
// l = 0
// st.sort()
// ed.sort()
// while i < 26 and j < 26:
// 	if st[i] == 0:
// 		i += 1
// 		continue
// 	if ed[j] == 0:
// 		j += 1
// 		continue
// 	if st[i] <= ed[j]:
// 		l += 1
// 		i += 1
// 		if l > maxi:
// 			maxi = l
// 	else:
// 		l -= 1
// 		j += 1
// if maxi > k:
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, string_: string) returns (output: string)
  requires n <= |string_|
  requires forall t :: 0 <= t < |string_| ==> 'A' <= string_[t] <= 'Z'
{
  var st := seq(26, _ => 0);
  var ed := seq(26, _ => 0);
  var idx := 0;
  while idx < n
    invariant 0 <= idx
    invariant |st| == 26
    invariant |ed| == 26
    decreases n - idx
  {
    var code := string_[idx] as int - 'A' as int;
    if st[code] == 0 {
      st := st[code := idx + 1];
    } else {
      ed := ed[code := idx + 1];
    }
    idx := idx + 1;
  }
  var i := 0;
  while i < 26
    invariant |st| == 26
    invariant |ed| == 26
    decreases 26 - i
  {
    if st[i] != 0 && ed[i] == 0 {
      ed := ed[i := st[i]];
    }
    i := i + 1;
  }
  st := SortInts(st);
  ed := SortInts(ed);
  var ii := 0;
  var jj := 0;
  var maxi := -1000000000;
  var l := 0;
  while ii < 26 && jj < 26
    decreases (26 - ii) + (26 - jj)
  {
    if st[ii] == 0 {
      ii := ii + 1;
    } else if ed[jj] == 0 {
      jj := jj + 1;
    } else if st[ii] <= ed[jj] {
      l := l + 1;
      ii := ii + 1;
      if l > maxi { maxi := l; }
    } else {
      l := l - 1;
      jj := jj + 1;
    }
  }
  if maxi > k {
    output := "YES";
  } else {
    output := "NO";
  }
}
