// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n+m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loops over s once and then n (the value k) times, each
//     iteration calling `MaxSeq` on the fixed 26 weights, so the cost is
//     O(|s| + k), a sum of two sizes, as in the Python.
//
//   how this label could be wrong, and what to check:
//     The label multiplies, but the Python's two loops are sequential: one
//     over |t| and one over the value k, whose body takes `max(w)` over 26
//     fixed weights. Check that the second loop is not nested in the first
//     and that w always has 26 entries; then the class is O(|s| + k).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 24, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "MaxSeq"],
//     "loop_depth": 1, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 447_B. DZY Loves Strings  (problem 700, solution 700_99)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = input()
// k = int(input())
// w = [int(x) for x in input().split()]
// total = 0
// for i in range(len(t)):
//     total = total + w[ord(t[i])-97]*(i+1)
// for i in range(k):
//     total = total + max(w)*(len(t)+i+1)
// print(total)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string, n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| == 26
  requires forall k :: 0 <= k < |s| ==> 'a' <= s[k] <= 'z'
{
  var total := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    var idx := (s[i] as int) - 97;
    total := total + a_list[idx] * (i + 1);
    i := i + 1;
  }
  i := 0;
  while i < n
    decreases n - i
  {
    total := total + MaxSeq(a_list) * (|s| + i + 1);
    i := i + 1;
  }
  output := IntToString(total);
}
