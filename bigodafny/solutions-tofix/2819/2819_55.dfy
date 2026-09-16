// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-21
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve's outer `while i >= 0 && !found` decrements kk by the
//     increasing value `right` each round, a triangular-number drain, so
//     it and the trailing `while kk > 0 { j := j-1 }` together cost O(n)
//     per test case, not O(n**2); the description caps the sum of n over
//     test cases at 1e5, matching linear total work in both Python and
//     Dafny.
//
//   how this label could be wrong, and what to check:
//     The label assumes the outer while loop over i (searching for the 'b'
//     positions) runs O(n) times for O(n) total inner work, giving
//     O(n**2). Check that kk decreases by the triangular value `right`
//     (1,2,3,...) each non-breaking iteration: since the cumulative
//     subtraction after m steps is ~m**2/2 and k is capped by n*(n-1)/2,
//     the loop breaks after O(n) steps total (not O(n) per each of O(n)
//     outer positions), and the subsequent inner `while kk` drains at most
//     `right`<=n more steps once. Confirm by tracing kk's decrements
//     against the description's k <= n*(n-1)/2 bound.
//
//   structural facts (deterministic, from labelaudit.py):
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
