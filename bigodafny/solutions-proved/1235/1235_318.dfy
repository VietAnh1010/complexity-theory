// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops once over the n test rows and the inner `while j < |l|`
//     counts odd entries of a 4-element row, a constant; the Python's `for
//     i in l` over four numbers is the same, so row width does not enter
//     and the cost is O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes a variable row width m. Check the input: each test
//     has exactly four counts r g b w, so the `while j < |l|` loop runs 4
//     times.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 33, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     2, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1395_A. Boboniu Likes to Color Balls  (problem 1235, solution 1235_318)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// testcases = int(input())
// 
// for i in range(testcases):
//     l = list(map(int , input().split()))
//     odd = 0
//     for i in l:
//         if(i%2 != 0):
//             odd+=1 
//     if(odd in (0,1,4)) or (odd == 3 and (0 not in (l[0],l[1],l[2]))):
//         print("Yes")
//     else:
//         print("No")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function RowsLen(m: seq<seq<int>>, k: nat): nat
  requires k <= |m|
  decreases k
{
  if k == 0 then 0 else RowsLen(m, k - 1) + |m[k - 1]|
}

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n == |matrix|
  requires forall k :: 0 <= k < n ==> |matrix[k]| >= 3
  ensures steps <= 6 * RowsLen(matrix, n) + 40 * n + 5
{
  steps := 1;
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |lines| == i
    invariant SumLen(lines) <= 3 * i
    invariant steps <= 6 * RowsLen(matrix, i) + 34 * i + 1
    decreases n - i
  {
    ghost var st0 := steps;
    var l := matrix[i];
    var odd := 0;
    var j := 0;
    steps := steps + 1;
    while j < |l|
      invariant 0 <= j <= |l|
      invariant steps <= st0 + 1 + 6 * j
      decreases |l| - j
    {
      if l[j] % 2 != 0 { odd := odd + 1; }
      j := j + 1;
      steps := steps + 6;
    }
    var cond1 := odd == 0 || odd == 1 || odd == 4;
    var cond2 := odd == 3 && l[0] != 0 && l[1] != 0 && l[2] != 0;
    steps := steps + 20;
    SumLenSnoc(lines, "Yes");
    SumLenSnoc(lines, "No");
    if cond1 || cond2 {
      lines := lines + ["Yes"];
    } else {
      lines := lines + ["No"];
    }
    steps := steps + 3;
    i := i + 1;
    assert RowsLen(matrix, i) == RowsLen(matrix, i - 1) + |matrix[i - 1]|;
  }
  output := Join(lines, "\n");
  steps := steps + SumLen(lines) + |lines|;
}
