// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     For each pair row, Solve allocates buf of size nn, walks i down from
//     nn-2 once, and the inner `while kk > 0` loop runs only at the found
//     position, so each test is O(nn) and the whole is O(sum nn_i), a
//     per-test value term. The Python's ['a']*n, zip loop with break, and
//     print(*ans) cost the same, so the O(n**2) label is wrong.
//
//   how this label could be wrong, and what to check:
//     The label treats n as if each test cost quadratic. Check the loop in
//     Solve: per test the `while i >= 0 && !found` loop runs at most nn
//     iterations and the inner `while kk > 0` runs once (found is then
//     set), so cost per test is linear in that test's nn; the total is
//     O(sum of the per-test n_i), not O(n**2) in the test count.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 53, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 3, "loops":
//     4, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1328_B. K-th Beautiful String  (problem 2819, solution 2819_55)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input = sys.stdin.readline
// 
// for _ in range(int(input())):
//     n, k = map(int, input().split())
//     ans = ['a']*n
//     for i, right in zip(range(n-2, -1, -1), range(1, n+1)):
//         if k > right:
//             k -= right
//             continue
//         j = n
//         while k:
//             k -= 1
//             j -= 1
// 
//         ans[i] = ans[j] = 'b'
//         break
// 
//     print(*ans, sep='')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  var results: seq<string> := [];
  var t := 0;
  while t < |pairs_list|
    invariant 0 <= t <= |pairs_list|
  {
    var row := pairs_list[t];
    if |row| >= 2 {
      var nn := row[0];
      var kk := row[1];
      var sz := if nn > 0 then nn else 0;
      var buf := new char[sz];
      var z := 0;
      while z < sz
        invariant 0 <= z <= sz
      {
        buf[z] := 'a';
        z := z + 1;
      }
      var i := nn - 2;
      var right := 1;
      var found := false;
      while i >= 0 && !found
        decreases i + 1
      {
        if kk > right {
          kk := kk - right;
        } else {
          var j := nn;
          var kk0 := kk;
          while kk > 0
            invariant j == nn - (kk0 - kk)
            decreases kk
          {
            kk := kk - 1;
            j := j - 1;
          }
          if 0 <= i < sz { buf[i] := 'b'; }
          if 0 <= j < sz { buf[j] := 'b'; }
          found := true;
        }
        i := i - 1;
        right := right + 1;
      }
      results := results + [buf[0..sz]];
    }
    t := t + 1;
  }
  output := Join(results, "\n");
}
