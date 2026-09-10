// 1827_44 (problem 1827) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n**2)
//   proved bound    : BIG * (XCAP + 2) + BIG * (XCAP + 2) + (a + BIG) * a + BIG * (a + 1)
//   proved class    : O(n**2+m**2)
//   agent verdict   : proves
//   reference label : O(n**2)
//   prediction correct against the label: True
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     S := S + [x] (seq append, cost |S|) sits inside a loop whose total
//     executed iterations are bounded by `sum` (via ss decreasing), so
//     cumulative append cost is quadratic in sum, same trap as the other
//     seq-append example; limit only bounds a log-depth Pow2 recursion,
//     dominated.
//
//   agent notes:
//     Two quadratic-risk spots: seq append |S|<=s (dominant), and Pow2
//     recomputed at growing depth in a loop (only log-scale, dominated once
//     limit is capped). Tracked |S|+ss<=s as a potential invariant to bound
//     total appends by s. 7/7 verified after adding two MulMonoRight calls
//     to unstick the final nonlinear postcondition.
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 1827_44
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
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
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Pow2(e: int): int
  requires e >= 0
  ensures Pow2(e) >= 1
  decreases e
{
  if e == 0 then 1 else 2 * Pow2(e - 1)
}

// Weak but cheap: Pow2 at least doubles each step, so in particular it grows
// past its own argument. Used only to turn the natural loop invariant
// Pow2(x) <= l into a numeral bound on x once l is capped.
lemma Pow2GeSucc(e: int)
  requires e >= 0
  ensures Pow2(e) >= e + 1
  decreases e
{
  if e > 0 { Pow2GeSucc(e - 1); }
}

lemma MulMonoRight(x: int, p: int, q: int)
  requires x >= 0 && p <= q
  ensures x * p <= x * q
{}

// Generous fixed constant: covers every O(1)/O(xcap) real cost in this method
// (map-free arithmetic, and every Pow2 call, whose argument is bounded by
// XCAP once `limit` is capped) except the seq append, whose real cost |S|
// is charged separately and honestly below.
ghost const BIG: nat := 3000000000000000000
ghost const XCAP: nat := 100000

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  requires a >= 0
  // Problem statement: 1 <= limit <= 10^5. Pow2's real cost is proportional
  // to its argument, and every Pow2 call here has an argument bounded by x,
  // which the loop below keeps at most `limit` -- without this cap that
  // recursion depth is unbounded in a way unrelated to either input's size.
  requires 1 <= b <= 100000
  ensures steps <= BIG * (XCAP + 2) + BIG * (XCAP + 2) + (a + BIG) * a + BIG * (a + 1)
{
  var s := a;
  var l := b;
  var x := 0;
  steps := 1;
  while Pow2(x + 1) <= l
    invariant x >= 0
    invariant Pow2(x) <= l
    invariant x <= XCAP
    invariant steps <= BIG * x + 5
    decreases l - Pow2(x + 1)
  {
    x := x + 1;
    steps := steps + BIG;
    Pow2GeSucc(x);
    // Pow2(x) <= l <= 100000 == XCAP, and Pow2(x) >= x + 1, so x <= XCAP.
  }
  ghost var stepsAfterFirstLoop := steps;
  assert stepsAfterFirstLoop <= BIG * x + 5;
  var S: seq<int> := [];
  var ss := s;
  var xx := x;
  while xx >= 0
    invariant ss >= 0
    invariant |S| + ss <= s
    invariant steps <= stepsAfterFirstLoop + BIG * (x - xx) + (s + BIG) * |S|
    decreases xx + 1
  {
    var aa := 1;
    while Pow2(xx) <= ss && aa * Pow2(xx) <= l
      invariant ss >= 0
      invariant |S| + ss <= s
      invariant steps <= stepsAfterFirstLoop + BIG * (x - xx) + (s + BIG) * |S|
      decreases ss
    {
      // real cost of this append is |S| (<= s, by the invariant above);
      // charged generously as the numeral bound s itself.
      S := S + [aa * Pow2(xx)];
      aa := aa + 2;
      ss := ss - Pow2(xx);
      steps := steps + s + BIG;
    }
    xx := xx - 1;
    steps := steps + BIG;
  }
  assert xx == -1;
  MulMonoRight(s + BIG, |S|, s);
  MulMonoRight(BIG, x, XCAP);
  assert steps <= (BIG * x + 5) + BIG * (x + 1) + (s + BIG) * s;
  if ss == 0 {
    output := IntToString(|S|) + "\n" + JoinInts(S, " ");
  } else {
    output := IntToString(-1);
  }
  // JoinInts' real cost is the sum of digit-lengths of |S| <= s elements,
  // each bounded (their value is capped by `limit`) -- folded generously.
  steps := steps + BIG * (s + 1);
}
