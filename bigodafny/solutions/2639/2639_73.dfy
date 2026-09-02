// 975_B. Mancala  (problem 2639, solution 2639_73)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = list(map(int, input().split()))
// 
// ans = 0
// for i in range(len(a)):
//     x = a[i]
//     b = [j for j in a]
//     b[i] = 0
//     for j in range(len(a)):
//         b[j] += x // 14
//     
//     for j in range(1, x % 14 + 1):
//         b[(i + j) % 14] += 1
//         
//     ans_now = 0
//     for j in b:
//         if j % 2 == 0:
//             ans_now += j
//     ans = max(ans_now, ans)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method DistributeMancala(a: seq<int>, i: int) returns (result: int)
  requires |a| == 14
  requires 0 <= i < 14
{
  var x := a[i];
  var b := a[i := 0];
  var q := if x >= 0 then x / 14 else 0;
  var j := 0;
  while j < 14
    invariant 0 <= j <= 14
    invariant |b| == 14
    decreases 14 - j
  {
    b := b[j := b[j] + q];
    j := j + 1;
  }
  var r := if x >= 0 then x % 14 else 0;
  var t := 1;
  while t <= r
    invariant |b| == 14
    decreases r - t
  {
    var idx := (i + t) % 14;
    b := b[idx := b[idx] + 1];
    t := t + 1;
  }
  var s := 0;
  var k := 0;
  while k < 14
    invariant 0 <= k <= 14
    invariant |b| == 14
    decreases 14 - k
  {
    if b[k] % 2 == 0 { s := s + b[k]; }
    k := k + 1;
  }
  result := s;
}

method Solve(values: seq<int>) returns (output: string)
  requires |values| == 14
{
  var ans := 0;
  var i := 0;
  while i < 14
    invariant 0 <= i <= 14
    decreases 14 - i
  {
    var ansNow := DistributeMancala(values, i);
    if ansNow > ans { ans := ansNow; }
    i := i + 1;
  }
  output := IntToString(ans);
}
