// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny inner loop adds one element to S per iteration, so it runs
//     at most O(min(sum, limit)) times in total, each calling Pow2(xx)
//     whose recursion costs only xx, a geometric-weighted sum that stays
//     O(limit). No construct is quadratic, and the Python's identical
//     while loop with 2 ** x is linear in the same values.
//
//   how this label could be wrong, and what to check:
//     The label assumes quadratic growth in a size n, but the input is two
//     values (sum, limit). Check how many times the innermost while loop
//     runs: each pass appends one element of S, and the output size is at
//     most limit, so the cost is linear in the values.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 44, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "JoinInts"],
//     "loop_depth": 2, "loops": 3, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 0,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 437_B. The Child and Set  (problem 1827, solution 1827_44)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import *
// 
// s, l = map(int, input().split())
// mL = floor(log2(l))
// mS = floor(log2(l))
// x = min(mL, mS)
// 
// S = []
// while x >= 0:
// 	a = 1
// 	while 2 ** x <= s and a * 2 ** x <= l:
// 		S.append(a * 2 ** x)
// 		a += 2
// 		s -= 2 ** x
// 	x -= 1
// if s == 0:
// 	print(len(S))
// 	print(' '.join(map(str, S)))
// else:
// 	print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Pow2(e: int): int
  requires e >= 0
  ensures Pow2(e) >= 1
  decreases e
{
  if e == 0 then 1 else 2 * Pow2(e - 1)
}

method Solve(a: int, b: int) returns (output: string)
  requires a >= 0
{
  var s := a;
  var l := b;
  var x := 0;
  while Pow2(x + 1) <= l
    decreases l - Pow2(x + 1)
  {
    x := x + 1;
  }
  var S: seq<int> := [];
  var ss := s;
  var xx := x;
  while xx >= 0
    invariant ss >= 0
    decreases xx + 1
  {
    var aa := 1;
    while Pow2(xx) <= ss && aa * Pow2(xx) <= l
      invariant ss >= 0
      decreases ss
    {
      S := S + [aa * Pow2(xx)];
      aa := aa + 2;
      ss := ss - Pow2(xx);
    }
    xx := xx - 1;
  }
  if ss == 0 {
    output := IntToString(|S|) + "\n" + JoinInts(S, " ");
  } else {
    output := IntToString(-1);
  }
}
