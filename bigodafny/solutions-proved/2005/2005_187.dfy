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
  requires K == 7 * n + 10
  ensures n * K == 7 * (n * n) + 10 * n
{
}

method Solve(n: int, numbers: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 0
  requires n == |numbers|
  ensures steps <= 14 * (n * n) + 22 * n + 10
{
  steps := 0;
  steps := steps + (1 + |"A"| * n as nat);
  var ans: seq<char> := Repeat("A", n as nat);
  RepeatLen("A", n as nat);
  ghost var K: nat := 7 * n + 10;
  Sq2005(n, K);
  var num := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |ans| == n
    invariant steps <= 1 + n + i * K
    decreases n - i
  {
    CostMulDistrib(i, 1, i + 1, K);
    steps := steps + 2;
    steps := steps + 1;
    var cnt, s1 := CountOcc2005(numbers, numbers[i]);
    steps := steps + s1;
    steps := steps + 1;
    if cnt <= 1 {
      steps := steps + 1;
      if num < 0 {
        steps := steps + 1;
        num := num + 1;
        steps := steps + 1;
        ans := ans[i := 'B'];
      } else {
        steps := steps + 1;
        num := num - 1;
      }
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  steps := steps + 1;
  if num < 0 {
    var j := 0;
    var stop := false;
    ghost var s00 := steps;
    while j < n && !stop
      invariant 0 <= j <= n
      invariant |ans| == n
      invariant steps <= s00 + j * K
      decreases n - j
    {
      CostMulDistrib(j, 1, j + 1, K);
      steps := steps + (3 + if j < n then 1 else 0);
      steps := steps + 1;
      var cnt2, s0 := CountOcc2005(numbers, numbers[j]);
      steps := steps + s0;
      steps := steps + 1;
      if cnt2 > 2 {
        steps := steps + 1;
        ans := ans[j := 'B'];
        num := 0;
        stop := true;
      }
      steps := steps + 1;
      j := j + 1;
    }
    assert j * K <= n * K by { CostMulMonoLeft(j, n, K); }
    steps := steps + (2 + if j < n then 1 else 0);
  }
  steps := steps + 1;
  if num == 0 {
    steps := steps + |ans|;
    output := "YES\n" + ans;
  } else {
    output := "NO";
  }
}

method CountOcc2005(a: seq<int>, x: int)
    returns (c: int, ghost steps: nat)
  ensures steps <= 7 * |a| + 2
{
  steps := 0;
  c := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant steps <= 7 * i
    decreases |a| - i
  {
    steps := steps + 3;
    steps := steps + 2;
    if a[i] == x {
      steps := steps + 1;
      c := c + 1;
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 2;
}

import opened Prelude
