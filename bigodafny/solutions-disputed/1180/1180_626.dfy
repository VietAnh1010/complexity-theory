// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)log(n+m)
//   audited class  : O(n+mlogm)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop advances either l_left (m letters) or d_left (at most
//     n dormitories) so it is O(n+m), and Sort(lst, ...) sorts only the m
//     answer pairs in O(m log m), giving O(n+mlogm), below the labelled
//     (n+m)log(n+m). The Python's sorted(lst) also sorts m entries, so the
//     label overstates the original too.
//
//   how this label could be wrong, and what to check:
//     The label applies a log factor to the combined size, but only the m
//     letter records are sorted. Check the Sort call on lst: its length is
//     m (one entry per letter), while the dormitory array of length n is
//     only walked by the d_left pointer.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 51, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 2, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts":
//     ["Sort"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 978_C. Letters  (problem 1180, solution 1180_626)
// time complexity: O(n+m)log(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n_dorm,n_letter = map(int,input().split())
// dorms = list(map(int,input().split()))[:n_dorm]
// lroom = list(map(int,input().split()))[:n_letter]
// d_left = 0
// d_right = len(dorms) - 1
// l_left = 0
// l_right = len(lroom) - 1
// lst = []
// new = 0
// while l_left <= l_right:
//     if lroom[l_left] <= dorms[d_left]:
//         lst.append([d_left+1] + [abs(new-lroom[l_left])])
//         l_left += 1
//     else:
//         d_left += 1
//         new = dorms[d_left-1]
//         dorms[d_left] += dorms[d_left - 1]
// for i in sorted(lst):
//     print(f"{i[0]} {i[1]}")  
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function PrefixSum1180(s: seq<int>, n: nat): int
  requires n <= |s|
{
  if n == 0 then 0 else PrefixSum1180(s, n-1) + s[n-1]
}

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
  requires a >= 1
  requires b >= 0
  requires a <= |c_list|
  requires b <= |d_list|
  requires forall k :: 0 <= k < b ==> d_list[k] >= 1 && d_list[k] <= PrefixSum1180(c_list, a)
{
  var dorms := c_list[..a];
  var lroom := d_list[..b];
  var d_left := 0;
  var l_left := 0;
  var l_right := b - 1;
  var lst: seq<(int,int)> := [];
  var new_val := 0;
  while l_left <= l_right
    invariant 0 <= d_left < a
    invariant 0 <= l_left <= l_right + 1 <= b
    invariant |dorms| == a
    invariant forall k :: 0 <= k < d_left ==> dorms[k] == PrefixSum1180(c_list, k+1)
    invariant dorms[d_left] == PrefixSum1180(c_list, d_left+1)
    invariant forall k :: d_left < k < a ==> dorms[k] == c_list[k]
    invariant lroom[l_left..b] == d_list[l_left..b]
    decreases l_right - l_left + 1, a - d_left
  {
    if lroom[l_left] <= dorms[d_left] {
      lst := lst + [(d_left + 1, AbsInt(new_val - lroom[l_left]))];
      l_left := l_left + 1;
    } else {
      d_left := d_left + 1;
      new_val := dorms[d_left - 1];
      dorms := dorms[d_left := dorms[d_left] + dorms[d_left - 1]];
    }
  }
  var sorted_lst := Sort(lst, (p: (int,int), q: (int,int)) => p.0 < q.0 || (p.0 == q.0 && p.1 < q.1));
  var lines: seq<string> := [];
  var i := 0;
  while i < |sorted_lst|
    decreases |sorted_lst| - i
  {
    lines := lines + [IntToString(sorted_lst[i].0) + " " + IntToString(sorted_lst[i].1)];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
