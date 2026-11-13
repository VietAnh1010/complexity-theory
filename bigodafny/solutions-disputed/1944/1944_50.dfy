// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     For each of the t test values the Dafny calls `ISqrt(numbers[i])`,
//     charged its O(log) recursion depth, so the cost is O(t log max s_i);
//     the Python's `math.ceil(math.sqrt(...))` takes the same square root.
//
//   how this label could be wrong, and what to check:
//     The label charges each test 1, but each test takes
//     `ISqrt(numbers[i])`, charged O(log s_i), a value term; the Python's
//     `math.sqrt` takes the same root. Check that the per-test work is
//     otherwise constant; then the class is O(t log max s_i).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 16, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1550_A. Find The Array  (problem 1944, solution 1944_50)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// t=int(input())
// for i in range(t):
//     print(math.ceil(math.sqrt(int(input()))))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |numbers|
    decreases |numbers| - i
  {
    var r := ISqrt(numbers[i]);
    if r * r < numbers[i] { r := r + 1; }
    parts := parts + [IntToString(r)];
    i := i + 1;
  }
  output := Join(parts, "\n") + "\n";
}
