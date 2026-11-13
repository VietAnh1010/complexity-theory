// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loops `while i * i <= n` incrementing i by one, about
//     sqrt(n) iterations with O(1) work each, so the cost is O(sqrt n);
//     the Python's loop has the identical guard.
//
//   how this label could be wrong, and what to check:
//     The label is linear in the input value n, but the loop stops at `i *
//     i <= n`, so it runs about sqrt(n) times. Check the loop guard in
//     both programs; the class is O(sqrt n), outside the vocabulary, hence
//     `other`.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 18, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 0,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1331_B. Limericks  (problem 1357, solution 1357_271)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// i = 2
// while i * i <= n:
//     if n % i == 0:
//         print(i, end='')
//         print(n // i,end='')
//     i += 1
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
{

  var i := 2;
  var parts: seq<string> := [];
  while i * i <= n
    decreases n - i*i
  {
    if n % i == 0 {
      parts := parts + [IntToString(i), IntToString(n / i)];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
}
