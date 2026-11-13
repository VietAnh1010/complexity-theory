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
//     Both programs read only `l[0]`, `l[1]` and `l[2]` of each of n query
//     rows and output one value, so the cost is O(n); a row is a fixed
//     triple, never walked.
//
//   how this label could be wrong, and what to check:
//     The label assumes row width varies. Each query is exactly three
//     integers n, s, t, and both programs read only `l[0]`, `l[1]`,
//     `l[2]`. Check the input format; three numbers per line make m a
//     constant and the class O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 20, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1187_A. Stickers and Toys  (problem 1231, solution 1231_51)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=int(input())
// for i in range(t):
//     l=list(map(int,input().split()))
//     print(max(l[0]-l[1],l[0]-l[2])+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n <= |a_list|
  requires forall k :: 0 <= k < |a_list| ==> |a_list[k]| >= 3
  ensures steps <= 17 * (if n > 0 then n else 0) + 2 * |output| + 2
{
  steps := 1;
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i
    invariant i <= n || n < 0
    invariant |lines| == i
    invariant steps <= 1 + 16 * i + SumLen(lines)
    decreases n - i
  {
    var l := a_list[i];
    var v1 := l[0] - l[1];
    var v2 := l[0] - l[2];
    var m := if v1 > v2 then v1 else v2;
    IntToStringDigits(m + 1);
    SumLenSnoc(lines, IntToString(m + 1));
    lines := lines + [IntToString(m + 1)];
    i := i + 1;
    steps := steps + 16 + Digits(m + 1);
  }
  output := Join(lines, "\n");
  steps := steps + SumLen(lines) + |lines|;
  if |lines| >= 1 { JoinLen(lines, "\n"); }
}
