// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(nlogn)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-11
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     fib is built by a while loop that stops once fib[|fib|-1]>n, so
//     |fib| is O(log n); the outer while i<=n then runs an inner while
//     k<|fib| every iteration, mirroring Python's `i in fib` linear scan,
//     giving O(n log n) total for both languages.
//
//   how this label could be wrong, and what to check:
//     The label assumes fib membership is O(1) per check. Confirm |fib|
//     grows only logarithmically because Fibonacci exceeds n after about
//     log_phi(n) terms, and that the inner while k<|fib| (and Python's `i
//     in fib`) rescans that whole list on every one of the n iterations of
//     i; if so the true cost is O(n log n), not O(n).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 38, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     3, "recursive_helpers": 0, "seq_append_read_in_same_loop": true,
//     "seq_args": 0, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 918_A. Eleven  (problem 1699, solution 1699_213)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// fib = [0, 1]
// while fib[-1] <= n:
//     fib.append(fib[-1] + fib[-2])
// name = ''
// for i in range(1,n+1):
//     if i in fib:
//         name += 'O'
//     else:
//         name += 'o'
// print(name) 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var fib := [0, 1];
  // the seed [0,1] repeats 1 once, so the last term is not yet strictly
  // increasing; the second component retires that one step.
  while fib[|fib| - 1] <= n
    invariant |fib| >= 2
    invariant fib[|fib| - 2] >= 0
    invariant fib[|fib| - 1] >= 1
    decreases n - fib[|fib| - 1] + 1, if fib[|fib| - 2] == 0 then 1 else 0
  {
    fib := fib + [fib[|fib| - 1] + fib[|fib| - 2]];
  }
  var parts: seq<string> := [];
  var i := 1;
  while i <= n
    decreases n - i + 1
  {
    var isFib := false;
    var k := 0;
    while k < |fib|
      invariant 0 <= k <= |fib|
      decreases |fib| - k
    {
      if fib[k] == i {
        isFib := true;
      }
      k := k + 1;
    }
    if isFib {
      parts := parts + ["O"];
    } else {
      parts := parts + ["o"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
