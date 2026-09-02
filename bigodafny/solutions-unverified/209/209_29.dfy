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

method Solve(N: int, numbers: seq<int>) returns (output: string)
{
  var a := numbers;
  var ans := 0;
  var brk := false;
  while |a| > 0 && !brk
    decreases (if brk then 0 else 1), |a|
  {
    var mxIdx := 0;
    var k := 1;
    while k < |a|
      invariant 0 <= mxIdx < |a|
      invariant 1 <= k <= |a|
      decreases |a| - k
    {
      if a[k] > a[mxIdx] { mxIdx := k; }
      k := k + 1;
    }
    var mx := a[mxIdx];
    if mx <= 0 {
      brk := true;
    } else {
      ans := ans + mx;
      a := a[..mxIdx] + a[mxIdx + 1..];
      var newA: seq<int> := [];
      var j := 0;
      while j < |a|
        invariant 0 <= j <= |a|
        invariant |newA| == j
        decreases |a| - j
      {
        if a[j] == mx {
          newA := newA + [a[j] - 1];
        } else {
          newA := newA + [a[j]];
        }
        j := j + 1;
      }
      a := newA;
    }
  }
  output := IntToString(ans);
}
