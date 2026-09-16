// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-batch-20
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     For an array of n/2 distinct values each repeated twice, count1 and
//     |d| are both Theta(n), and for every outer i the inner scan needs
//     roughly n/2 steps to exhaust all distinct values, each step doing f
//     := f[e := cur] at map size Theta(n); that is Theta(n) outer times
//     Theta(n) inner times Theta(n) per write, giving O(n**3) for the
//     Dafny versus O(n**2) for Pythons O(1) dict writes and O(n) dict copy
//     per outer step.
//
//   how this label could be wrong, and what to check:
//     The label matches the Pythons O(n**2) (dict copy plus O(1) writes in
//     the nested pref/suf-style scan), but the Dafny inner loop writes f
//     := f[e := cur], a map update costing O(|f|). Construct a case with
//     Theta(n) distinct values each appearing exactly twice (so |d| and
//     count1 are both Theta(n)); check whether the inner scan length stays
//     Theta(n) for Theta(n) outer iterations, which would make the
//     map-write cost compound to O(n**3) in Dafny while Python stays
//     O(n**2).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 49, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 3, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": true,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1208_B. Uniqueness  (problem 2650, solution 2650_153)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// lst = [int(i) for i in input().split()]
// d, count1 = {}, 0
// for elem in lst:
//     d[elem] = d.get(elem, 0) + 1
//     if d[elem] == 2:
//         count1 += 1
// result = n
// if len(d) == n:
//     result = 0
// for i in range(n):
//     f = d.copy()
//     count2 = count1
//     for j in range(i, n):
//         f[lst[j]] -= 1
//         if f[lst[j]] == 1:
//             count2 -= 1
//         if count2 == 0:
//             result = min(result, j - i + 1)
//             break
// print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  requires n >= 1
{
  var d: map<int, int> := map[];
  var count1 := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var e := a_list[i];
    var cur := if e in d then d[e] else 0;
    d := d[e := cur + 1];
    if cur + 1 == 2 { count1 := count1 + 1; }
    i := i + 1;
  }
  var result := n;
  if |d| == n { result := 0; }
  i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var f := d;
    var count2 := count1;
    var j := i;
    var brk := false;
    while j < n && !brk
      invariant i <= j <= n
      decreases n - j
    {
      var e := a_list[j];
      var cur := (if e in f then f[e] else 0) - 1;
      f := f[e := cur];
      if cur == 1 { count2 := count2 - 1; }
      if count2 == 0 {
        var cand := j - i + 1;
        if cand < result { result := cand; }
        brk := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  output := IntToString(result);
}
