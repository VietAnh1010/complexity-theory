// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(logn)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     curr_div increments by 1 on each failed trial division with no
//     sqrt(n) cutoff, so a large prime factor in a forces curr_div up
//     toward the magnitude of a itself before n % curr_div == 0 fires;
//     sibling row 310_51 runs the identical increment strategy for the
//     same problem 797A, explicitly bounded to 2*i<=n, and is labeled O(n)
//     -- the same worst case applies here to both this Dafny and the
//     identical Python increment logic, so O(logn) understates it.
//
//   structural facts (deterministic, from labelaudit.py):
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
