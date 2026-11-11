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

include "../../../../prelude.dfy"

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n == |a_list|
  ensures steps <= (SumLg(a_list) + 1) * PassCost(n) + 6 * n + 2 + |output|
{
  steps := 0;
  var no := a_list;
  var flag := true;
  ghost var pinit := SumLg(a_list);
  ghost var c: nat := 0;
  while flag
    invariant |no| == n
    invariant steps <= c * PassCost(n)
    invariant c + SumLg(no) <= pinit + (if flag then 0 else 1)
    decreases SumLg(no) + (if flag then 1 else 0)
  {
    ghost var sp := steps;
    ghost var p0 := SumLg(no);
    steps := steps + 1;
    flag := false;
    var oi := 0;
    while oi < n
      invariant 0 <= oi <= n
      invariant |no| == n
      invariant steps <= sp + 1 + oi * PassK(n)
      invariant SumLg(no) <= p0
      invariant flag ==> SumLg(no) < p0
      decreases n - oi
    {
      steps := steps + 2;
      steps := steps + 1;
      var iv := no[oi];
      steps := steps + 1;
      if iv > 0 {
        ghost var s1 := steps;
        var j := 0;
        while j < n
          invariant 0 <= j <= n
          invariant |no| == n
          invariant steps <= s1 + 11 * j
          invariant SumLg(no) <= p0
          invariant flag ==> SumLg(no) < p0
          decreases n - j
        {
          steps := steps + 2;
          steps := steps + 2;
          if no[j] > iv {
            flag := true;
            steps := steps + 3;
            ModFacts(no[j], iv);
            if no[j] % iv == 0 {
              steps := steps + 1;
              LgHalf(iv, no[j]);
              SumLgSet(no, j, iv);
              no := no[j := iv];
            } else {
              steps := steps + 3;
              LgHalf(no[j] % iv, no[j]);
              SumLgSet(no, j, no[j] % iv);
              no := no[j := no[j] % iv];
            }
          }
          steps := steps + 1;
          j := j + 1;
        }
        steps := steps + 1;
      }
      steps := steps + 1;
      CostMulDistrib(oi, 1, oi + 1, PassK(n));
      oi := oi + 1;
    }
    steps := steps + 1;
    CostMulDistrib(c, 1, c + 1, PassCost(n));
    c := c + 1;
  }
  CostMulMonoLeft(c, pinit + 1, PassCost(n));
  ghost var base := steps;
  var total := 0;
  var k := 0;
  while k < |no|
    invariant 0 <= k <= |no|
    invariant steps <= base + 6 * k
    decreases |no| - k
  {
    steps := steps + 3;
    steps := steps + 2;
    total := total + no[k];
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 2;
  steps := steps + Digits(total);
  IntToStringDigits(total);
  output := IntToString(total);
}

import opened Prelude

ghost function PassK(n: nat): nat { 11 * n + 6 }
ghost function PassCost(n: nat): nat { n * PassK(n) + 2 }

ghost function Lg(x: int): nat
  decreases if x < 0 then 0 else x
{
  if x <= 0 then 0 else 1 + Lg(x / 2)
}

ghost function SumLg(s: seq<int>): nat
  decreases |s|
{
  if |s| == 0 then 0 else SumLg(s[..|s| - 1]) + Lg(s[|s| - 1])
}

lemma LgMono(x: int, y: int)
  requires x <= y
  ensures Lg(x) <= Lg(y)
  decreases if y < 0 then 0 else y
{
  if x > 0 { LgMono(x / 2, y / 2); }
}

lemma LgHalf(y: int, x: int)
  requires 0 < y && 2 * y <= x
  ensures Lg(y) < Lg(x)
{
  LgMono(y, x / 2);
}

lemma SumLgSet(s: seq<int>, j: nat, v: int)
  requires j < |s|
  ensures SumLg(s[j := v]) + Lg(s[j]) == SumLg(s) + Lg(v)
  decreases |s|
{
  var t := s[j := v];
  if j == |s| - 1 {
    assert t[..|s| - 1] == s[..|s| - 1];
  } else {
    assert t[..|s| - 1] == s[..|s| - 1][j := v];
    SumLgSet(s[..|s| - 1], j, v);
  }
}

lemma ModFacts(x: int, m: int)
  requires 0 < m < x
  ensures x % m == 0 ==> 2 * m <= x
  ensures x % m != 0 ==> 0 < x % m && 2 * (x % m) < x
{
  var q := x / m;
  var r := x % m;
  assert x == q * m + r && 0 <= r < m;
  if q <= 0 { assert q * m <= 0 by { assert (-q) * m >= 0; } }
  assert q >= 1;
  assert q * m >= m by { assert (q - 1) * m >= 0; }
  if r == 0 && q == 1 { assert q * m == m; }
  if r == 0 && q >= 2 { assert q * m >= 2 * m by { assert (q - 2) * m >= 0; } }
}
