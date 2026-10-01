// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-d02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over n queries and per query runs `while x * (x - 1) / 2
//     < val`, about sqrt(2*val) iterations, then Repeat("7", remN) and
//     Repeat("3", threesN), costing O(x); this is a per-test value term,
//     not O(n**2). The Python has the same `while (x * (x - 1) // 2 < n)`
//     loop and string repeats.
//
//   how this label could be wrong, and what to check:
//     The label counts the number of queries n, but the cost is dominated
//     by a loop bounded by a per-test value. Check `while x * (x - 1) / 2
//     < val`: it runs about sqrt(2*val) times for each test value, which
//     the label's n does not include.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 34, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["Join", "Repeat"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1202_D. Print a 1337-string...  (problem 1867, solution 1867_45)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input = sys.stdin.readline
// from math import floor, sqrt, log
// 
// q = int(input())
// for _ in range(q):
// 	#a = c = 1
// 	n = int(input())
// 	if n == 1:
// 		print("1337")
// 		continue
// 	x = 2
// 	while (x * (x - 1) // 2 < n):
// 		x += 1
// 	x -= 1
// 	n -= x * (x - 1) // 2
// 	print("133", end = '')
// 	print('7' * n, end = '')
// 	print('3' * (x - 2), end = '')
// 	print('7')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
  requires n >= 0
  requires |numbers| >= n
{
  var lines: seq<string> := [];
  var qi := 0;
  while qi < n
    invariant 0 <= qi <= n
    decreases n - qi
  {
    var val := numbers[qi];
    if val == 1 {
      lines := lines + ["1337"];
    } else {
      var x := 2;
      while x * (x - 1) / 2 < val
        decreases val - x * (x - 1) / 2
      {
        x := x + 1;
      }
      x := x - 1;
      var rem := val - x * (x - 1) / 2;
      var remN := if rem < 0 then 0 else rem;
      var threes := x - 2;
      var threesN := if threes < 0 then 0 else threes;
      var ans := "133" + Repeat("7", remN) + Repeat("3", threesN) + "7";
      lines := lines + [ans];
    }
    qi := qi + 1;
  }
  output := Join(lines, "\n");
}
