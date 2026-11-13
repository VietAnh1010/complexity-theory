// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both programs read only the four fixed entries of each of n test
//     rows and print b, c, c, so the cost is O(n); a row is never walked.
//
//   how this label could be wrong, and what to check:
//     The label assumes row width varies. Each test case is exactly four
//     integers a, b, c, d, read as `l[0]` to `l[3]`. Check the input
//     format; four numbers per line make m a constant and the class O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 24, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1337_A. Ichihime and Triangle  (problem 2325, solution 2325_862)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// for i in range(n):
//     l=list(map(int,input().split()))
//     a,b,c,d=l[0],l[1],l[2],l[3]
//     x=b
//     y=c
//     z=c
//     print(x,y,z)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
  requires n <= |lists|
  requires forall k :: 0 <= k < |lists| ==> |lists[k]| >= 4
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var l := lists[i];
    var a := l[0];
    var b := l[1];
    var c := l[2];
    var d := l[3];
    var x := b;
    var y := c;
    var z := c;
    parts := parts + [IntToString(x) + " " + IntToString(y) + " " + IntToString(z)];
    i := i + 1;
  }
  output := Join(parts, "\n");
}
