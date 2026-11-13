// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : both
//   confidence     : low
//   auditor        : labelaudit-r4-d02
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     Solve takes two integers and its loops run to log l and to the
//     number of elements added (bounded by the values s and l), each
//     iteration calling the recursive Pow2, whose depth is the exponent,
//     so the cost is a value term like O(s log l), not O(n**2). The Python
//     uses 2 ** x as one operation, so the Dafny's extra Pow2 recursion is
//     a reimplemented-library overhead; the true class is outside the
//     vocabulary.
//
//   how this label could be wrong, and what to check:
//     The label names a size n, but the signature has only two values s
//     and l and no collection. Check Pow2 (recursion on the exponent)
//     called inside `while Pow2(xx) <= ss && aa * Pow2(xx) <= l`: each
//     call costs its exponent depth, and the loop appends up to s/2^xx
//     items per level.
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

ghost function Lm(b: int): nat { if b > 1 then b else 1 }

ghost function Flog(L: nat): nat
  decreases L
{
  if L < 2 then 0 else 1 + Flog(L / 2)
}

ghost function Qf(f: nat): nat { 4 * f + 16 }

lemma Pow2LeFlog(x: nat, L: nat)
  requires L >= 1 && Pow2(x) <= L
  ensures x <= Flog(L)
  decreases x
{
  if x > 0 {
    assert Pow2(x) == 2 * Pow2(x - 1);
    Pow2LeFlog(x - 1, L / 2);
  }
}

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  requires a >= 0
  ensures steps <= 40 + Flog(Lm(b)) * (Flog(Lm(b)) + 9) + Qf(Flog(Lm(b))) * a
                  + Qf(Flog(Lm(b))) * (Flog(Lm(b)) + 1) + 3 * |output|
{
  steps := 2;
  var s := a;
  var l := b;
  var x := 0;
  while Pow2(x + 1) <= l
    invariant 0 <= x
    invariant Pow2(x) <= Lm(b)
    invariant steps <= 2 + x * (x + 8)
    decreases l - Pow2(x + 1)
  {
    assert Pow2(x + 1) == 2 * Pow2(x);
    steps := steps + x + 5;
    assert (x + 1) * (x + 9) == x * (x + 8) + 2 * x + 9;
    x := x + 1;
  }
  steps := steps + x + 2;
  Pow2LeFlog(x, Lm(b));
  ghost var F := Flog(Lm(b));
  ghost var Q := Qf(F);
  CostMulMonoLeft(x, F, x + 8);
  CostMulMono(F, x + 8, F + 8);
  var S: seq<int> := [];
  var ss := s;
  var xx := x;
  ghost var cnt: nat := 0;
  ghost var lvl: nat := 0;
  ghost var base := steps;
  assert F * (F + 9) == F * (F + 8) + F;
  assert base <= 4 + F * (F + 9);
  while xx >= 0
    invariant ss >= 0 && xx <= x
    invariant lvl == x - xx
    invariant cnt + ss <= s
    invariant |S| == cnt
    invariant steps <= base + Q * cnt + Q * lvl
    decreases xx + 1
  {
    CostMulDistrib(lvl, 1, lvl + 1, Q);
    lvl := lvl + 1;
    steps := steps + Q;
    var aa := 1;
    while Pow2(xx) <= ss && aa * Pow2(xx) <= l
      invariant ss >= 0
      invariant cnt + ss <= s
      invariant |S| == cnt
      invariant steps <= base + Q * cnt + Q * lvl
      decreases ss
    {
      S := S + [aa * Pow2(xx)];
      aa := aa + 2;
      ss := ss - Pow2(xx);
      CostMulDistrib(cnt, 1, cnt + 1, Q);
      cnt := cnt + 1;
      steps := steps + Q;
    }
    xx := xx - 1;
  }
  assert lvl == x + 1;
  CostMulMono(Q, cnt, a);
  CostMulMono(Q, x + 1, F + 1);
  if ss == 0 {
    IntToStringDigits(|S|);
    if |S| >= 1 { JoinIntsLen(S, " "); } else { assert SumDigits(S) == 0; }
    output := IntToString(|S|) + "\n" + JoinInts(S, " ");
    steps := steps + Digits(|S|) + 2 + SumDigits(S) + |S| + |JoinInts(S, " ")| + 2;
  } else {
    IntToStringDigits(-1);
    output := IntToString(-1);
    steps := steps + 2;
  }
}
