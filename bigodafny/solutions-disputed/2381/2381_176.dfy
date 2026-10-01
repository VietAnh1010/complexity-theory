// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop in Solve increments ans while BinAsDecimal(ans) <= n,
//     which exits after about 2**(number of decimal digits of n), roughly
//     n**0.3 iterations, each paying BinAsDecimal's recursion depth
//     log2(ans); the cost is a value term of about n**0.3 * log n,
//     sublinear in n. The Python runs the same loop with
//     int(bin(ans)[2:]), so the loose O(n) label is the cause, not the
//     translation.
//
//   how this label could be wrong, and what to check:
//     The label treats the loop as running to n, but ans only counts up to
//     the largest number of 0/1 decimal digits at most n, so the iteration
//     count is about n**0.30 (2**d for a d-digit n). Check the loop
//     condition `BinAsDecimal(ans) <= n`: BinAsDecimal is monotone in ans,
//     so the loop stops after roughly 2**(digits of n) iterations, not n.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 19, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 9_C. Hexadecimal's Numbers  (problem 2381, solution 2381_176)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,ans=int(input()),1
// while int(bin(ans)[2:])<=n:
//     ans+=1
// print(ans-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function BinAsDecimal(x: int): int
  decreases if x < 0 then 0 else x
{
  if x <= 0 then 0
  else BinAsDecimal(x / 2) * 10 + x % 2
}

method Solve(n: int) returns (output: string)
  decreases *
{
  var ans := 1;
  while BinAsDecimal(ans) <= n
    decreases *
  {
    ans := ans + 1;
  }
  output := IntToString(ans - 1);
}
