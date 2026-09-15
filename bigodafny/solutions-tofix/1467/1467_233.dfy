// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-09
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The only parameter is the scalar N, and the description caps it at
//     "1 <= n <= 1000"; the loop `while i < N + 100` is bounded by this
//     capped value rather than by the size of any passed-in sequence, so
//     per the value-bounded-loop rule the whole computation is bounded by
//     a constant regardless of N.
//
//   how this label could be wrong, and what to check:
//     The label treats N as an unbounded growth axis, but this signature
//     has no seq argument at all (seq_args is 0) and N is the only
//     parameter. Compare against sibling 1467_532, which solves the
//     identical problem, encodes the same domain as `requires 1 <= N <=
//     1000`, and is labeled O(1); check whether this row's weaker
//     `requires N >= 0` is an incomplete precondition rather than a real
//     unbounded domain. If the description's "1 <= n <= 1000" is the
//     intended domain, the while loop bounded by N+100 never runs more
//     than about 1100 times and the row's O(n) is the same bug as its
//     sibling's fix shows it should not be.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 42, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 2,
//     "seq_append_read_in_same_loop": false, "seq_args": 0,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 672_A. Summer Camp  (problem 1467, solution 1467_233)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// t=''
// for i in range(n+100):
//     t+=str(i)
// print(t[n])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma IntToStringLen(x: int)
  ensures |IntToString(x)| >= 1
  decreases if x < 0 then 1 - x else x
{
  if x < 0 { IntToStringLen(-x); }
  else if x < 10 {
  } else {
    IntToStringLen(x / 10);
  }
}

lemma JoinEmptySepLen(parts: seq<string>)
  requires forall k :: 0 <= k < |parts| ==> |parts[k]| >= 1
  ensures |Join(parts, "")| >= |parts|
  decreases |parts|
{
  if |parts| == 0 {
  } else if |parts| == 1 {
  } else {
    JoinEmptySepLen(parts[1..]);
  }
}

method Solve(N: int) returns (output: string)
  requires N >= 0
{
  var parts: seq<string> := [];
  var i := 0;
  while i < N + 100
    invariant 0 <= i
    invariant |parts| == i
    invariant forall k :: 0 <= k < |parts| ==> |parts[k]| >= 1
    decreases N + 100 - i
  {
    IntToStringLen(i);
    parts := parts + [IntToString(i)];
    i := i + 1;
  }
  JoinEmptySepLen(parts);
  var t := Join(parts, "");
  output := [t[N]];
}
