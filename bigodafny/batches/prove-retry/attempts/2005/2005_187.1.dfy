// 1051_C. Vasya and Multisets  (problem 2005, solution 2005_187)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import *
// n = int(input())
// a = list(map(int,input().split()))
// ans = ["A"]*n
// num = 0
// for i in range(n):
//     if a.count(a[i])>1:
//         continue
//     if num<0:
//         num+=1
//         ans[i] = "B"
//     else:
//         num-=1
// if num<0:
//     for i in range(n):
//         if a.count(a[i])<=2:
//             continue
//         ans[i] = "B"
//         num= 0
//         break
// if num==0:
//     print("YES")
//     print(*ans,sep = '')
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma RepeatLen(s: string, n: nat)
  ensures |Repeat(s, n)| == n * |s|
  decreases n
{
  if n == 0 {
  } else {
    RepeatLen(s, n - 1);
  }
}

lemma Sq2005(n: nat, K: nat)
  requires K == 5 * n + 2
  ensures n * K == 5 * (n * n) + 2 * n
{
}

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires n == |numbers|
  ensures steps <= 12 * (n * n) + 20 * n + 20
{
  steps := 1;
  var ans: seq<char> := Repeat("A", n as nat);
  RepeatLen("A", n as nat);
  steps := steps + n;
  ghost var K: nat := 5 * n + 2 + 6;
  var num := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |ans| == n
    invariant steps <= 1 + n + i * K
    decreases n - i
  {
    var cnt, cs := CountOcc2005(numbers, numbers[i]);
    if cnt <= 1 {
      if num < 0 {
        num := num + 1;
        ans := ans[i := 'B'];
      } else {
        num := num - 1;
      }
    }
    CostMulDistrib(i, 1, i + 1, K);
    i := i + 1;
    steps := steps + cs + 6;
  }
  Sq2005(n, 5 * n + 2);
  assert n * K == n * (5 * n + 2) + 6 * n by { CostMulDistrib(n, 0, n, 0); }
  if num < 0 {
    var j := 0;
    var stop := false;
    ghost var s0 := steps;
    while j < n && !stop
      invariant 0 <= j <= n
      invariant |ans| == n
      invariant steps <= s0 + j * K
      decreases n - j
    {
      var cnt2, cs := CountOcc2005(numbers, numbers[j]);
      if cnt2 > 2 {
        ans := ans[j := 'B'];
        num := 0;
        stop := true;
      }
      CostMulDistrib(j, 1, j + 1, K);
      j := j + 1;
      steps := steps + cs + 6;
    }
    assert j * K <= n * K by { CostMulMonoLeft(j, n, K); }
  }
  if num == 0 {
    output := "YES\n" + ans;
    steps := steps + |ans| + 1;
  } else {
    output := "NO";
    steps := steps + 1;
  }
}

method CountOcc2005(a: seq<int>, x: int) returns (c: int, ghost steps: nat)
  ensures steps <= 5 * |a| + 2
{
  steps := 1;
  c := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant steps == 1 + 5 * i
    decreases |a| - i
  {
    if a[i] == x {
      c := c + 1;
    }
    i := i + 1;
    steps := steps + 5;
  }
}
