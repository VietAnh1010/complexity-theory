// 1409_C. Yet Another Array Restoration  (problem 794, solution 794_794)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input = sys.stdin.readline
//
// def solve():
//     n,x,y=map(int,input().split())
//     arr = []
//     for i in range(1,n):
//         if (y-x)%i==0:
//             step = (y-x)//i
//             smol = x%step
//             if smol == 0:
//                 smol+=step
//             total = smol+step*(n-1)
//             arr.append((max(total,y),step))
//
//     total,step = min(arr)
//     print(*range(total-step*(n-1),total+1,step))
//
// if __name__=="__main__":
//     for _ in range(int(input())):
//         solve()
// --------------------------------------------------------------------
//
// The label O(n) counts n = |data|, the number of test cases. Per-test work
// is driven by the VALUE data[t].0 (the test's own "n"), not by |data|: the
// two inner loops each run data[t].0 times. COMPLEXITY.md's "value versus
// size" convention says that value counts as its own parameter, so the bound
// this file proves is linear in the SUM of the per-test values, not in the
// number of tests -- looser-structural, not confirms.

include "../../../../prelude.dfy"
import opened Prelude

method Solve(n: int, data: seq<(int, int, int)>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |data| ==> data[k].0 >= 2 && 0 <= data[k].1 < data[k].2
  ensures steps <= 20 * PrefixSum(seq(|data|, k requires 0 <= k < |data| => data[k].0), |data|) + 20 * |data| + 2
{
  ghost var firsts := seq(|data|, k requires 0 <= k < |data| => data[k].0);
  steps := 1;
  output := "";
  var t := 0;
  while t < |data|
    invariant 0 <= t <= |data|
    invariant steps <= 1 + 20 * PrefixSum(firsts, t) + 20 * t
    decreases |data| - t
  {
    var (nn, x, y) := data[t];
    var arr: seq<(int, int)> := [];
    var i := 1;
    while i < nn
      invariant 1 <= i <= nn
      invariant i > 1 ==> |arr| >= 1
      invariant |arr| <= i - 1
      invariant forall k :: 0 <= k < |arr| ==> arr[k].1 > 0
      invariant steps <= 1 + 20 * PrefixSum(firsts, t) + 20 * t + 6 * (i - 1)
      decreases nn - i
    {
      if (y - x) % i == 0 {
        assert i <= y - x;
        var step := (y - x) / i;
        assert step > 0;
        var smol := x % step;
        if smol == 0 { smol := smol + step; }
        var total := smol + step * (nn - 1);
        var m := if y > total then y else total;
        arr := arr + [(m, step)];
      }
      i := i + 1;
      steps := steps + 6;
    }
    var best := arr[0];
    var j := 1;
    while j < |arr|
      invariant 1 <= j <= |arr|
      invariant best.1 > 0
      invariant steps <= 1 + 20 * PrefixSum(firsts, t) + 20 * t + 6 * (nn - 1) + 3 * (j - 1)
      decreases |arr| - j
    {
      if arr[j].0 < best.0 || (arr[j].0 == best.0 && arr[j].1 < best.1) {
        best := arr[j];
      }
      j := j + 1;
      steps := steps + 3;
    }
    var total := best.0;
    var step := best.1;
    var start := total - step * (nn - 1);
    var vals: seq<int> := [];
    var v := start;
    var cnt3 := 0;
    while v <= total
      invariant step > 0
      invariant v == start + cnt3 * step
      invariant 0 <= cnt3 <= nn
      invariant steps <= 1 + 20 * PrefixSum(firsts, t) + 20 * t + 9 * (nn - 1) + 2 * cnt3
      decreases total - v
    {
      vals := vals + [v];
      v := v + step;
      cnt3 := cnt3 + 1;
      steps := steps + 2;
    }
    output := output + JoinInts(vals, " ") + "\n";
    steps := steps + 20;
    assert PrefixSum(firsts, t + 1) == PrefixSum(firsts, t) + nn;
    t := t + 1;
  }
}
