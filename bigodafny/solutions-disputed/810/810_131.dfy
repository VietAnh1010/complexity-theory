// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n log v)
//   cause          : label
//   confidence     : high
//   auditor        : value-vs-size convention, 2026-09-17
//
//   The label disagrees with the code under the value-versus-size
//   convention. BigOBench fitted its labels by profiling, which treats a
//   capped input value as constant; COMPLEXITY.md section 1 decides the
//   opposite. This row is where the two disagree.
//
//   evidence:
//     The label omits a value-derived factor. IntSqrt binary-searches
//     over the value a*b rather than over the query count, so each query
//     costs log of that value. Under the convention decided 2026-09-17 a
//     loop bounded by an input VALUE counts as a parameter, so the true
//     class carries a log v factor that O(n) does not.
//
//   how this label could be wrong, and what to check:
//     Open the Dafny and confirm IntSqrt's loop bound is derived from
//     the argument's magnitude, not from |pairs|. If it is, O(n)
//     understates the cost by exactly that factor. The proof in
//     solutions-proved/810/810_131.dfy already states the correct bound
//     and is unaffected by this move.
//
//   note: the translation is NOT at fault in any of these four rows. The
//   proof in solutions-proved/ is correct and stays there.
// --------------------------------------------------------------------

// p03388 AtCoder Beginner Contest 093 - Worst Case  (problem 810, solution 810_131)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// q=int(input())
// ab=[list(map(int,input().split())) for _ in range(q)]
// from math import floor
// for a,b in ab:
//   if a==b:
//     print(2*a-2)
//     continue
//   t=floor((a*b)**0.5)
//   # t,t+1 組み合わせの積がa*bで抑えられているかどうか
//   if t*t>=a*b: # t*tもだめ
//     print(2*t-3)
//   elif t*(t+1)>=a*b: # t*(t+1)はだめ
//     print(2*t-2)
//   else: # t*tもt*(t+1)もOK
//     print(2*t-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2 && pairs[k][0] >= 0 && pairs[k][1] >= 0
{
  output := "";
  var idx := 0;
  while idx < |pairs|
    invariant 0 <= idx <= |pairs|
    decreases |pairs| - idx
  {
    var a := pairs[idx][0];
    var b := pairs[idx][1];
    if a == b {
      output := output + IntToString(2 * a - 2) + "\n";
    } else {
      var t := IntSqrt(a * b);
      if t * t >= a * b {
        output := output + IntToString(2 * t - 3) + "\n";
      } else if t * (t + 1) >= a * b {
        output := output + IntToString(2 * t - 2) + "\n";
      } else {
        output := output + IntToString(2 * t - 1) + "\n";
      }
    }
    idx := idx + 1;
  }
}

method IntSqrt(x: int) returns (r: int)
  requires x >= 0
{
  if x == 0 {
    return 0;
  }
  var lo := 0;
  var hi := x + 1;
  while lo + 1 < hi
    invariant 0 <= lo < hi
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if mid * mid <= x {
      lo := mid;
    } else {
      hi := mid;
    }
  }
  r := lo;
}
