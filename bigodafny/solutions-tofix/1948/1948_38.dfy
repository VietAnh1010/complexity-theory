// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-13
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop 'while 2*a>m*m+m: m:=m+1' runs O(sqrt(a)) times, and a is
//     capped at 500 per the problem statement, so the iteration count is a
//     fixed bound regardless of any growing size; the Python's identical
//     while loop is bounded the same way, so O(n) mislabels what is really
//     a constant-time computation.
//
//   how this label could be wrong, and what to check:
//     Compare against sibling 1948_388, labelled O(1) for a similarly
//     bounded search. Confirm the input a is capped at 500 by the problem
//     statement ('1<=n<=500'), which bounds 'while 2*a>m*m+m' to about
//     sqrt(2a)<=32 iterations; if so the cost does not grow with any
//     exposed size and O(n) is the wrong label.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 18, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 0, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 47_A. Triangular numbers  (problem 1948, solution 1948_38)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = int(input())
// n = 1
// 
// while 2*a>n**2+n:
// 	n +=1
// 
// if (2*a)-(n**2+n)==0:
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
  decreases *
{
  var a := n;
  var m := 1;
  while 2 * a > m * m + m
    decreases *
  {
    m := m + 1;
  }
  if 2 * a - (m * m + m) == 0 {
    output := "YES";
  } else {
    output := "NO";
  }
}
