// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Per test the Dafny fills buf (nn cells), scans i from nn-2 down with
//     at most nn steps, runs the inner `while kk > 0` once for at most nn
//     steps, and copies buf[0..sz], so each test costs O(nn) and the total
//     over the test list is O(n*m), not O(n**2). The Python's ['a']*n, the
//     zip loop and the one while k loop pay the same.
//
//   how this label could be wrong, and what to check:
//     The label squares one size, but the loops are per test and linear in
//     that test's n. Check that the array fill `while z < sz`, the scan
//     `while i >= 0 && !found` and the inner `while kk > 0` are sequential
//     or bounded by nn, and none runs to nn inside another loop to nn.
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
