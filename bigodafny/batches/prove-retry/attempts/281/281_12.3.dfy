// 389_A. Fox and Number Game  (problem 281, solution 281_12)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = eval(input())
// no = list(map(eval,input().split()))
// while True:
//     flag = False
//     for i in no:
//         if i<=0:
//             continue
//         for j in range(n):
//             if no[j]>i:
//                 flag = True
//                 if no[j]%i == 0:
//                     no[j] = i
//                 else:
//                     no[j] = no[j]%i
//     if flag == False:
//         break
// # print(no)
// sum = 0
// for i in no:
//     sum += i
// print(int(sum))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function P(x: int): nat { if x > 0 then x else 0 }

ghost function SP(s: seq<int>): nat
  decreases |s|
{ if |s| == 0 then 0 else P(s[0]) + SP(s[1..]) }

lemma SPUpd(s: seq<int>, j: nat, x: int)
  requires j < |s|
  ensures SP(s[j := x]) + P(s[j]) == SP(s) + P(x)
  decreases |s|
{
  if j > 0 {
    SPUpd(s[1..], j - 1, x);
    assert s[j := x][1..] == s[1..][j - 1 := x];
  } else {
    assert s[0 := x][1..] == s[1..];
  }
}

ghost function PassCost(n: nat): nat { n * (8 * n + 6) + 3 }

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  ensures steps <= (SP(a_list) + 1) * PassCost(n) + 4 * n + |output| + 10
{
  steps := 1;
  var no := a_list;
  var flag := true;
  ghost var rounds: nat := 0;
  ghost var b0 := steps;
  while flag
    invariant |no| == n
    invariant SP(no) + rounds <= SP(a_list) + (if flag then 0 else 1)
    invariant steps <= b0 + rounds * PassCost(n)
    decreases SP(no) + (if flag then 1 else 0)
  {
    ghost var sp0 := SP(no);
    ghost var b1 := steps;
    flag := false;
    var oi := 0;
    while oi < n
      invariant 0 <= oi <= n
      invariant |no| == n
      invariant SP(no) <= sp0
      invariant flag ==> SP(no) < sp0
      invariant steps <= b1 + oi * (8 * n + 6)
      decreases n - oi
    {
      var iv := no[oi];
      steps := steps + 6;
      ghost var b2 := steps;
      if iv > 0 {
        var j := 0;
        while j < n
          invariant 0 <= j <= n
          invariant |no| == n
          invariant SP(no) <= sp0
          invariant flag ==> SP(no) < sp0
          invariant steps <= b2 + 8 * j
          decreases n - j
        {
          if no[j] > iv {
            flag := true;
            if no[j] % iv == 0 {
              SPUpd(no, j, iv);
              no := no[j := iv];
            } else {
              SPUpd(no, j, no[j] % iv);
              no := no[j := no[j] % iv];
            }
          }
          j := j + 1;
          steps := steps + 8;
        }
      }
      CostMulDistrib(oi, 1, oi + 1, 8 * n + 6);
      oi := oi + 1;
    }
    assert flag ==> SP(no) < sp0;
    CostMulDistrib(rounds, 1, rounds + 1, PassCost(n));
    rounds := rounds + 1;
    steps := steps + 3;
  }
  CostMulMonoLeft(rounds, SP(a_list) + 1, PassCost(n));
  var total := 0;
  var k := 0;
  ghost var b3 := steps;
  while k < |no|
    invariant 0 <= k <= |no|
    invariant steps == b3 + 4 * k
    decreases |no| - k
  {
    total := total + no[k];
    k := k + 1;
    steps := steps + 4;
  }
  output := IntToString(total);
  IntToStringDigits(total);
  steps := steps + |output| + 1;
}
