// 750_A. New Year and Hurry  (problem 704, solution 704_614)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #NEW YEAR AND HURRY
//
// n,hrs = map(int,input().split())
// cnt = 0
// res = 0
// l = []
//
// if hrs > 240:
//     print(0)
// else:
//     for i in range(1,n+1):
//         ans = 5*i
//         hrs += (ans)
//         if hrs <= 240:
//             cnt += 1
//
// print(cnt)
//
// --------------------------------------------------------------------

include "../../../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  requires a >= 0
  ensures steps <= 6 * a + 5
{
  steps := 1;
  var cnt := 0;
  var hrs := b;
  if hrs > 240 {
    output := "0";
    steps := steps + 1;
  } else {
    steps := steps + 1;
    var i := 1;
    while i <= a
      invariant 1 <= i <= a + 1
      invariant steps <= 6 * (i - 1) + 2
      decreases a - i + 1
    {
      var ans := 5 * i;
      hrs := hrs + ans;
      if hrs <= 240 {
        cnt := cnt + 1;
        steps := steps + 1;
      }
      steps := steps + 1;
      i := i + 1;
      steps := steps + 4;   // 5*i (1) + hrs+ans (1) + comparison (1) + i+1 (1)
    }
    output := IntToString(cnt);
    steps := steps + 1;
  }
}
