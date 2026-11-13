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
//     Solve loops t < n over the test cases and the inner `while i < 2`
//     and `while j < 2` loops are fixed-size, reading a[i], b[j] from
//     2-element rows; no loop walks a row of variable width, so the cost
//     is O(n) in the test count and the Python has the same shape.
//
//   how this label could be wrong, and what to check:
//     The label assumes a row-width dimension m. Check the input format:
//     each test gives two dimension pairs, so a and b are always 2-element
//     rows, and the 2x2 inner loops are constant.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 36, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 3, "loops":
//     3, "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1351_B. Square?  (problem 1018, solution 1018_421)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #By maxwill, contest: Testing Round #16 (Unrated), problem: (B) Square?, Compilation error, #, Copy
// T = int(input().strip())
// for i in range(T):
//     a = list(map(int, input().strip().split()))
//     b = list(map(int, input().strip().split()))
//     flag = False
//     for i in range(2):
//         for j in range(2):
//             if(a[i] == b[j] and a[1-i]+b[1-j] == a[i]):
//                 flag = True
//     
//     print("Yes" if flag else "No" ) 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |edges| == 2 * n
  requires forall k :: 0 <= k < |edges| ==> |edges[k]| == 2
  ensures steps <= 64 * n + 3
{
  steps := 1;
  var lines: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    invariant |lines| == t
    invariant SumLen(lines) <= 3 * t
    invariant steps == 1 + 60 * t
    decreases n - t
  {
    ghost var s0 := steps;
    steps := steps + 6;
    var a := edges[2 * t];
    var b := edges[2 * t + 1];
    var flag := false;
    var i := 0;
    while i < 2
      invariant 0 <= i <= 2
      invariant steps == s0 + 6 + 24 * i
      decreases 2 - i
    {
      var j := 0;
      ghost var s1 := steps;
      while j < 2
        invariant 0 <= j <= 2
        invariant steps == s1 + 10 * j
        decreases 2 - j
      {
        if a[i] == b[j] && a[1 - i] + b[1 - j] == a[i] {
          flag := true;
        }
        j := j + 1;
        steps := steps + 10;
      }
      i := i + 1;
      steps := steps + 4;
    }
    SumLenSnoc(lines, if flag then "Yes" else "No");
    lines := lines + [if flag then "Yes" else "No"];
    t := t + 1;
    steps := steps + 60 - 54;
  }
  output := Join(lines, "\n");
  steps := steps + SumLen(lines) + |lines|;
}
