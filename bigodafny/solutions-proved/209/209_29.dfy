// 624_B. Making a String  (problem 209, solution 209_29)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// rng = [int(t) for t in input().split()]
//
// ans = 0
// while len(rng) != 0:
//     mx = max(rng)
//
//     if mx <= 0:
//         break
//
//     ans += mx
//
//     rng.remove(mx)
//     for i in range(len(rng)):
//         if rng[i] == mx:
//             rng[i] -= 1
//
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Isolated multiplication: (c+1)*K == c*K + K.
lemma MulDistribAdd(c: int, K: int)
  ensures (c + 1) * K == c * K + K
{}

// Isolated monotonicity: a <= b, c >= 0 ==> c*a <= c*b.
lemma MulMonoLeft(a: int, b: int, c: int)
  requires a <= b
  requires c >= 0
  ensures c * a <= c * b
{}

method Solve(N: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 3 + (12 * |numbers| + 6) * (|numbers| + 1)
{
  steps := 1;
  var a := numbers;
  var ans := 0;
  var brk := false;
  ghost var outerCnt := 0;
  while |a| > 0 && !brk
    invariant |a| <= |numbers|
    invariant outerCnt <= (|numbers| - |a|) + (if brk then 1 else 0)
    invariant steps <= 1 + (12 * |numbers| + 6) * outerCnt
    decreases (if brk then 0 else 1), |a|
  {
    var mxIdx := 0;
    var k := 1;
    steps := steps + 2;
    ghost var ibase1 := steps;
    while k < |a|
      invariant 0 <= mxIdx < |a|
      invariant 1 <= k <= |a|
      invariant steps <= ibase1 + 5 * (k - 1)
      decreases |a| - k
    {
      if a[k] > a[mxIdx] { mxIdx := k; }
      k := k + 1;
      steps := steps + 5;
    }
    var mx := a[mxIdx];
    steps := steps + 1;
    ghost var lenBefore := |a|;
    if mx <= 0 {
      brk := true;
      steps := steps + 1;
    } else {
      ans := ans + mx;
      steps := steps + 2;
      a := a[..mxIdx] + a[mxIdx + 1..];
      steps := steps + 2 + lenBefore;
      var newA: seq<int> := [];
      steps := steps + 1;
      var j := 0;
      ghost var ibase2 := steps;
      while j < |a|
        invariant 0 <= j <= |a|
        invariant |newA| == j
        invariant steps <= ibase2 + 4 * j
        decreases |a| - j
      {
        if a[j] == mx {
          newA := newA + [a[j] - 1];
        } else {
          newA := newA + [a[j]];
        }
        j := j + 1;
        steps := steps + 4;
      }
      a := newA;
    }
    ghost var cOld := outerCnt;
    outerCnt := outerCnt + 1;
    assert steps <= 1 + (12 * |numbers| + 6) * cOld + 12 * |numbers| + 6;
    assert (cOld + 1) * (12 * |numbers| + 6) == cOld * (12 * |numbers| + 6) + (12 * |numbers| + 6)
      by { MulDistribAdd(cOld, 12 * |numbers| + 6); }
  }
  assert outerCnt <= |numbers| + 1;
  assert (12 * |numbers| + 6) * outerCnt <= (12 * |numbers| + 6) * (|numbers| + 1)
    by { MulMonoLeft(outerCnt, |numbers| + 1, 12 * |numbers| + 6); }
  output := IntToString(ans);
  steps := steps + 1;
}
