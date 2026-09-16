// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-12
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Every append to `S`/`S.append` reduces the running `ss`/`s` by at
//     least `Pow2(xx)`/`2**x` >= 1, so across all levels of `xx` the total
//     number of appends is capped by the initial `s` (<=1e5 per the
//     constraint), making the whole build O(n) rather than the O(n**2) the
//     nested-loop shape suggests, in both Dafny and Python.
//
//   how this label could be wrong, and what to check:
//     The label assumes the double `while xx >= 0 { while Pow2(xx) <= ss
//     ... }` loop structure is quadratic in the value n=sum/limit. Check
//     that every successful inner iteration strictly decreases `ss` by
//     `Pow2(xx) >= 1`; since `ss` starts at `s <= 1e5` and the loop stops
//     appending once `ss` runs out, the total number of appends across
//     every level `xx` is bounded by `s`, not by (number of levels) x
//     (appends per level), so the true cost is O(n) in the value of s/l,
//     and Python's identical `s -= 2**x` accounting gives it the same O(n)
//     bound.
//
//   structural facts (deterministic, from labelaudit.py):
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
