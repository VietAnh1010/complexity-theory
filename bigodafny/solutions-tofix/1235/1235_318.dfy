// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The inner `while j < |l|` loop scans `l`, but per the problem
//     statement l is always the four values r,g,b,w, so its length is a
//     fixed constant, not a growing m; the Python's `for i in l` loop is
//     the same fixed-size scan, so both are O(n), not O(n*m).
//
//   how this label could be wrong, and what to check:
//     The label assumes row width m grows with n. Check the problem
//     statement: each test case always has exactly r,g,b,w (four balls),
//     so `matrix[k]` is a fixed-width row of length >=3; if width never
//     varies m is a constant, not a real dimension.
//
//   structural facts (deterministic, from labelaudit.py):
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

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
  requires n == |matrix|
  requires forall k :: 0 <= k < n ==> |matrix[k]| >= 3
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var l := matrix[i];
    var odd := 0;
    var j := 0;
    while j < |l|
      invariant 0 <= j <= |l|
      decreases |l| - j
    {
      if l[j] % 2 != 0 { odd := odd + 1; }
      j := j + 1;
    }
    var cond1 := odd == 0 || odd == 1 || odd == 4;
    var cond2 := odd == 3 && l[0] != 0 && l[1] != 0 && l[2] != 0;
    if cond1 || cond2 {
      lines := lines + ["Yes"];
    } else {
      lines := lines + ["No"];
    }
    i := i + 1;
  }
  output := Join(lines, "\n");
}
