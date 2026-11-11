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

include "../../../../prelude.dfy"

lemma RepeatLen(s: string, n: nat)
  ensures |Repeat(s, n)| == n * |s|
  decreases n
{
  if n == 0 {
  } else {
    RepeatLen(s, n - 1);
  }
}

method Solve(n: int, numbers: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 0
  requires n == |numbers|
  ensures steps <= 2 * (n * (7 * n + 11)) + 2 * n + 10
{
  steps := 0;
  steps := steps + (1 + |"A"| * n as nat);
  var ans: seq<char> := Repeat("A", n as nat);
  RepeatLen("A", n as nat);
  var num := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |ans| == n
    invariant steps <= 1 + n + i * (7 * n + 11)
    decreases n - i
  {
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
    CostMulDistrib(i - 1, 1, i, 7 * n + 11);
  }
  CostMulMonoLeft(i, n, 7 * n + 11);
  steps := steps + 1;
  steps := steps + 1;
  if num < 0 {
    var j := 0;
    var stop := false;
    ghost var base := steps;
    while j < n && !stop
      invariant 0 <= j <= n
      invariant |ans| == n
      invariant steps <= base + j * (7 * n + 11)
      decreases n - j
    {
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
      CostMulDistrib(j - 1, 1, j, 7 * n + 11);
    }
    CostMulMonoLeft(j, n, 7 * n + 11);
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
