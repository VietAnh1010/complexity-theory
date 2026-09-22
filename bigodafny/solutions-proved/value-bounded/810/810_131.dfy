// VALUE-BOUNDED -- filed for review; the proof carries a term the label omits.
//
//   This proof's bound depends on the MAGNITUDE of an input, not only on how
//   many inputs there are. BigOBench fitted the label by profiling, which
//   treats a capped value as constant; COMPLEXITY.md section 1 decides the
//   opposite, so the two disagree here by construction.
//
//   See solutions-proved/value-bounded/README.md for the category and
//   MANIFEST.jsonl for this row's entry.
//
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

include "../../../prelude.dfy"
import opened Prelude

// IntSqrt is a binary search over the VALUE a*b, not over q = |pairs|. Its
// iteration count is CeilLog2(a*b + 1), a quantity that grows with the input
// values and is independent of q. The per-query cost is therefore not O(1)
// the way an O(n)-over-q label implicitly assumes; this is a genuine second
// parameter (same shape as the value-magnitude note in PROMPT.md).
ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

lemma CeilLog2Monotone(m: nat, n: nat)
  requires m <= n
  ensures CeilLog2(m) <= CeilLog2(n)
  decreases n
{
  if n <= 1 { }
  else if m <= 1 { }
  else { CeilLog2Monotone((m + 1) / 2, (n + 1) / 2); }
}

method IntSqrt(x: int) returns (r: int, ghost steps: nat)
  requires x >= 0
  ensures steps <= 2 * CeilLog2(x + 1) + 4
{
  steps := 1;
  if x == 0 {
    steps := steps + 1;
    return 0, steps;
  }
  var lo := 0;
  var hi := x + 1;
  steps := steps + 2;
  while lo + 1 < hi
    invariant 0 <= lo < hi <= x + 1
    invariant steps <= 2 * (CeilLog2(x + 1) - CeilLog2(hi - lo)) + 3
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    var w := hi - lo;
    if mid * mid <= x {
      assert hi - mid == (w + 1) / 2;
      lo := mid;
    } else {
      assert mid - lo == w / 2 <= (w + 1) / 2;
      hi := mid;
    }
    CeilLog2Monotone(hi - lo, (w + 1) / 2);
    steps := steps + 2;
  }
  r := lo;
  steps := steps + 1;
}

// Sum, over the queries seen so far, of the value-dependent IntSqrt cost.
// This -- not q alone -- is the honest measure of this loop's work.
ghost function SumQueryCost(pairs: seq<seq<int>>, upto: nat): nat
  requires upto <= |pairs|
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2 && pairs[k][0] >= 0 && pairs[k][1] >= 0
{
  if upto == 0 then 0
  else SumQueryCost(pairs, upto - 1) + CeilLog2(pairs[upto - 1][0] * pairs[upto - 1][1] + 1)
}

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2 && pairs[k][0] >= 0 && pairs[k][1] >= 0
  ensures steps <= 8 * SumQueryCost(pairs, |pairs|) + 10 * |pairs| + 2
{
  steps := 1;
  output := "";
  var idx := 0;
  while idx < |pairs|
    invariant 0 <= idx <= |pairs|
    invariant steps <= 8 * SumQueryCost(pairs, idx) + 10 * idx + 1
    decreases |pairs| - idx
  {
    var a := pairs[idx][0];
    var b := pairs[idx][1];
    if a == b {
      output := output + IntToString(2 * a - 2) + "\n";
      steps := steps + 6;
    } else {
      var t, tsteps := IntSqrt(a * b);
      steps := steps + tsteps;
      if t * t >= a * b {
        output := output + IntToString(2 * t - 3) + "\n";
      } else if t * (t + 1) >= a * b {
        output := output + IntToString(2 * t - 2) + "\n";
      } else {
        output := output + IntToString(2 * t - 1) + "\n";
      }
      steps := steps + 6;
    }
    idx := idx + 1;
  }
}
