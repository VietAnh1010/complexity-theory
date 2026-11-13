// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over the tests once; per test, Repeat("9", cnt9) +
//     Repeat("8", cnt8) builds nv digits, so the cost is tests times the
//     per-test length, O(n*m) under the naming rule, not O(n**2). The
//     Python builds ['9'] * (n - ceil(n/4)) and joins it, the same linear
//     cost per test. If nv is read as a value rather than a size the class
//     would be other.
//
//   how this label could be wrong, and what to check:
//     The label looks for quadratic work, but the loop runs once per test
//     and builds a string of nv digits. Check Repeat("9", cnt9) and
//     Repeat("8", cnt8): they cost the per-test digit count nv, and
//     nothing nests inside another loop over the same size.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 24, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join", "Repeat"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1388_B. Captain Flint and a Long Voyage  (problem 721, solution 721_169)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil
// t = int(input())
// for _ in range(t):
//     n = int(input())
//     s = []
//     if n == 1:
//         print(8)
//     else:
//         s = ['9'] * (n - int(ceil(n / 4)))
//         s += ['8'] * int(ceil(n / 4))
//     print(''.join(s))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma RepLen(s: string, k: nat)
  requires |s| == 1
  ensures |Repeat(s, k)| == k
{
}

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 12 * |numbers| + 4 * |output| + 4
{
  steps := 1;
  var parts: seq<string> := [];
  var i := 0;
  while i < n && i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |parts| == i
    invariant steps <= 1 + 12 * i + 3 * SumLen(parts)
    decreases n - i
  {
    ghost var prev := parts;
    var nv := numbers[i];
    steps := steps + 4;
    if nv == 1 {
      parts := parts + ["8\n" + "\n"];
      steps := steps + 1 + 1;
    } else if nv > 0 {
      var cnt8 := (nv + 3) / 4;
      var cnt9 := nv - cnt8;
      RepLen("9", cnt9);
      RepLen("8", cnt8);
      parts := parts + [Repeat("9", cnt9) + Repeat("8", cnt8) + "\n"];
      steps := steps + 4 + cnt9 + cnt8 + cnt8 + 1 + 1;
    } else {
      parts := parts + ["\n"];
      steps := steps + 1;
    }
    SumLenSnoc(prev, parts[|parts| - 1]);
    i := i + 1;
  }
  output := Join(parts, "");
  if |parts| >= 1 {
    JoinLen(parts, "");
  }
  steps := steps + SumLen(parts) + |parts| + 1;
}
