// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(logn)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     In Solve the loop increments curr_div one step at a time up to the
//     largest prime factor of a, so a prime input costs O(a) iterations, a
//     value term far above O(log n); the Python has the same
//     trial-division loop.
//
//   how this label could be wrong, and what to check:
//     The label assumes cost logarithmic in n, but the trial division loop
//     increments curr_div by 1 until it divides n. Check `curr_div :=
//     curr_div + 1` in the else branch: for prime n and k=2 it climbs all
//     the way to n; the Python's while loop is identical.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 28, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": ["JoinInts"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 797_A. k-Factorization  (problem 310, solution 310_121)
// time complexity: O(logn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = [int(x) for x in input().split()]
// 
// sols = []
// curr_div = 2
// while n != 1 and len(sols) < k-1:
//     if n % curr_div == 0:
//         sols.append(curr_div)
//         n //= curr_div
//     else:
//         curr_div += 1
// 
// if len(sols) == k-1 and n != 1:
//     sols += [n]
//     sols = [str(x) for x in sols]
//     res = " ".join(sols)
//     print(res)
// else:
//     print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
  requires a >= 1
  decreases *
{
  var n := a;
  var k := b;
  var sols: seq<int> := [];
  var curr_div := 2;
  while n != 1 && |sols| < k - 1
    invariant 1 <= n
    decreases *
  {
    if n % curr_div == 0 {
      sols := sols + [curr_div];
      n := n / curr_div;
    } else {
      curr_div := curr_div + 1;
    }
  }
  if |sols| == k - 1 && n != 1 {
    sols := sols + [n];
    output := JoinInts(sols, " ") + "\n";
  } else {
    output := "-1\n";
  }
}
