// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-18
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop increments ans while BinAsDecimal(ans)<=n; since
//     problem constraints cap n at 1e9, ans need only reach about 2^9 to
//     2^10 before its binary-as-decimal reading exceeds n, so the loop is
//     bounded near a constant few hundred iterations for every legal n,
//     and the same brute-force Python loop has identical iteration count.
//
//   how this label could be wrong, and what to check:
//     The label assumes iterations of the ans-loop scale with n, but
//     BinAsDecimal(ans) reads ans's binary digits as a decimal literal, so
//     it grows roughly 10x per extra bit of ans while ans itself only
//     grows 2x; it exceeds n=1e9 once ans has about 10 bits, i.e. ans
//     reaches roughly 512-1024. Trace BinAsDecimal(512) and
//     BinAsDecimal(1023) against n=10**9 to confirm the loop always exits
//     within a few hundred steps for any n in the stated 1<=n<=1e9 range,
//     i.e. the iteration count is capped by the constraint, not by n's
//     magnitude.
//
//   structural facts (deterministic, from labelaudit.py):
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
