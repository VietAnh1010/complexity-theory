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
//     Both programs read only `row[0]` to `row[3]` of each of n test cases
//     and output one maximum, so the cost is O(n); a row is a fixed
//     four-tuple, never walked.
//
//   how this label could be wrong, and what to check:
//     The label assumes row width varies. Each test case is exactly four
//     integers a, b, c, d (the Dafny requires `|matrix[k]| == 4`), read as
//     `m[0]` to `m[3]`. Check the input format; a fixed four-number row
//     makes m a constant and the class O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 18, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1445_B. Elimination  (problem 914, solution 914_14)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for j in range(t):
// 	m=list(map(int,input().split()))
// 	a=m[0]+m[1]
// 	b=m[2]+m[3]
// 	if a>b:
// 		print(a)
// 	else:
// 		print(b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |matrix| ==> |matrix[k]| == 4
  ensures steps <= 14 * |matrix| + |output| + 3
{
  steps := 1;
  output := "";
  var i := 0;
  while i < |matrix|
    invariant 0 <= i <= |matrix|
    invariant steps <= 14 * i + |output| + 1
    decreases |matrix| - i
  {
    var row := matrix[i];
    var a := row[0] + row[1];
    var b := row[2] + row[3];
    var mx := if a > b then a else b;
    IntToStringDigits(mx);
    output := output + IntToString(mx) + "\n";
    steps := steps + 13 + Digits(mx);
    i := i + 1;
  }
  steps := steps + 2;
}
