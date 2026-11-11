// --- Python ---------------------------------------------------------
// def f(bs):
//     return int(bs, 2) // (1 << n - 1) * a[-1] + sum(a[i] for i in range(min(n - 1, len(bs))) if bs[-i - 1] == '1')
// n, x = map(int, input().split())
// *a, = map(int, input().split())
// for i in range(1, n):
//     a[i] = min(a[i], 2 * a[i - 1])
// bx = '0' * n + bin(x)[2:]
// ans = f(bx)
// for i in range(len(bx)):
//     if bx[i] == '0':
//         ans = min(ans, f(bx[:i] + '1' + '0' * (len(bx) - i - 1)))
// print(ans)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n: int, total_score: int, scores: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1
  requires |scores| == n
  requires total_score >= 0
  ensures steps <= 38 * ((n + Bits(total_score)) * (n + Bits(total_score))) + 109 * (n + Bits(total_score)) + 50 + |output|
{
  steps := 0;
  var x := total_score;
  var a := scores;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |a| == n
    invariant steps <= 12 * (i - 1)
    decreases n - i
  {
    steps := steps + 2;
    steps := steps + 3;
    var cand := 2 * a[i - 1];
    steps := steps + (4 + if a[i] < cand then 1 else 0);
    a := a[i := if a[i] < cand then a[i] else cand];
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  steps := steps + (|"0"| * n + IntToBinary90_steps(x) + |IntToBinary90(x)|);
  var bx := Repeat("0", n) + IntToBinary90(x);
  steps := steps + FCost90_steps(bx, n, a);
  var ans := FCost90(bx, n, a);
  RepLen(n);
  BinLen(x);
  FCostSteps(bx, n, a);
  assert |"0"| == 1;
  ghost var M := n + Bits(total_score);
  assert |bx| == M;
  ghost var K := 38 * M + 60;
  assert steps <= 49 * |bx| + 43;
  var j := 0;
  while j < |bx|
    invariant 0 <= j <= |bx|
    invariant steps <= 49 * |bx| + 43 + j * K
    decreases |bx| - j
  {
    steps := steps + 3;
    steps := steps + 2;
    if bx[j] == '0' {
      RepLen(|bx| - j - 1);
      assert |"1"| == 1;
      steps := steps + (4 + |"1"| + |"0"| * (|bx| - j - 1) + |Repeat("0", |bx| - j - 1)|);
      var candStr := bx[..j] + "1" + Repeat("0", |bx| - j - 1);
      assert |candStr| == |bx|;
      FCostSteps(candStr, n, a);
      steps := steps + FCost90_steps(candStr, n, a);
      var candVal := FCost90(candStr, n, a);
      steps := steps + 2;
      ans := if candVal < ans then candVal else ans;
    }
    steps := steps + 1;
    MulStep(j, K);
    j := j + 1;
  }
  Mul2(j, K, M);
  steps := steps + 2;
  steps := steps + (Digits(ans) + |"\n"|);
  IntToStringDigits(ans);
  output := IntToString(ans) + "\n";
}

function Pow2_90(e: int): int
  requires e >= 0
  ensures Pow2_90(e) >= 1
  decreases e
{
  if e == 0 then
    1
  else
    2 * Pow2_90(e - 1)
}

ghost function Pow2_90_steps(e: int): nat
  requires e >= 0
  decreases e
{
  2 + if e == 0 then 0 else 2 + Pow2_90_steps(e - 1)
}

function ParseBinary90(bs: string): int
  decreases |bs|
{
  if |bs| == 0 then
    0
  else
    ParseBinary90(bs[..|bs| - 1]) * 2 + if bs[|bs| - 1] == '1' then 1 else 0
}

ghost function ParseBinary90_steps(bs: string): nat
  decreases |bs|
{
  3 + if |bs| == 0 then 0 else 10 + ParseBinary90_steps(bs[..|bs| - 1])
}

function IntToBinaryPos90(x: int): string
  requires x >= 1
  decreases x
{
  if x == 1 then
    "1"
  else
    IntToBinaryPos90(x / 2) + [if x % 2 == 1 then '1' else '0']
}

ghost function IntToBinaryPos90_steps(x: int): nat
  requires x >= 1
  decreases x
{
  2 + if x == 1 then 0 else 5 + IntToBinaryPos90_steps(x / 2) + |[if x % 2 == 1 then '1' else '0']|
}

function IntToBinary90(x: int): string
  requires x >= 0
{
  if x == 0 then
    "0"
  else
    IntToBinaryPos90(x)
}

ghost function IntToBinary90_steps(x: int): nat
  requires x >= 0
{
  2 + if x == 0 then 0 else IntToBinaryPos90_steps(x)
}

function LowSum90(bs: string, a: seq<int>, i: int, limit: int): int
  decreases limit - i
{
  if i >= limit || i < 0 || limit > |bs| || limit > |a| then
    0
  else
    (if bs[|bs| - 1 - i] == '1' then a[i] else 0) + LowSum90(bs, a, i + 1, limit)
}

ghost function LowSum90_steps(bs: string, a: seq<int>, i: int, limit: int): nat
  decreases limit - i
{
  5 + (if i >= limit then 0 else 1) + (if i >= limit || i < 0 then 0 else 2) + (if i >= limit || i < 0 || limit > |bs| then 0 else 2) + if i >= limit || i < 0 || limit > |bs| || limit > |a| then 0 else 8 + (if bs[|bs| - 1 - i] == '1' then 1 else 0) + LowSum90_steps(bs, a, i + 1, limit)
}

function FCost90(bs: string, n: int, a: seq<int>): int
  requires n >= 1
  requires |a| == n
{
  var L := |bs|;
  var lim := if n - 1 <= L then n - 1 else L;
  ParseBinary90(bs) / Pow2_90(n - 1) * a[n - 1] + LowSum90(bs, a, 0, lim)
}

ghost function FCost90_steps(bs: string, n: int, a: seq<int>): nat
  requires n >= 1
  requires |a| == n
{
  10 + var L := |bs|; (if n - 1 <= L then 1 else 0) + var lim := if n - 1 <= L then n - 1 else L; ParseBinary90_steps(bs) + Pow2_90_steps(n - 1) + LowSum90_steps(bs, a, 0, lim)
}

ghost function Bits(x: int): nat
  requires x >= 0
  decreases x
{
  if x <= 1 then 1 else 1 + Bits(x / 2)
}

lemma RepLen(k: nat)
  ensures |Repeat("0", k)| == k
  decreases k
{
  if k > 0 { RepLen(k - 1); }
}

lemma BinPosLen(x: int)
  requires x >= 1
  ensures |IntToBinaryPos90(x)| == Bits(x)
  ensures IntToBinaryPos90_steps(x) <= 8 * Bits(x)
  decreases x
{
  if x > 1 { BinPosLen(x / 2); }
}

lemma BinLen(x: int)
  requires x >= 0
  ensures |IntToBinary90(x)| == Bits(x)
  ensures IntToBinary90_steps(x) <= 8 * Bits(x) + 2
{
  if x >= 1 { BinPosLen(x); }
}

lemma ParseSteps(bs: string)
  ensures ParseBinary90_steps(bs) == 3 + 13 * |bs|
  decreases |bs|
{
  if |bs| > 0 { ParseSteps(bs[..|bs| - 1]); }
}

lemma Pow2Steps(e: int)
  requires e >= 0
  ensures Pow2_90_steps(e) == 2 + 4 * e
  decreases e
{
  if e > 0 { Pow2Steps(e - 1); }
}

lemma LowSumSteps(bs: string, a: seq<int>, i: int, limit: int)
  ensures LowSum90_steps(bs, a, i, limit) <= 19 * (if limit > i then limit - i else 0) + 19
  decreases if limit > i then limit - i else 0
{
  if i < limit && i >= 0 && limit <= |bs| && limit <= |a| {
    LowSumSteps(bs, a, i + 1, limit);
  }
}

lemma FCostSteps(bs: string, n: int, a: seq<int>)
  requires n >= 1
  requires |a| == n
  ensures FCost90_steps(bs, n, a) <= 13 * |bs| + 23 * n + 40
{
  ParseSteps(bs);
  Pow2Steps(n - 1);
  var lim := if n - 1 <= |bs| then n - 1 else |bs|;
  LowSumSteps(bs, a, 0, lim);
}

lemma MulStep(j: int, K: int)
  ensures (j + 1) * K == j * K + K
{
}

lemma Mul2(j: int, K: int, M: int)
  requires j == M && K == 38 * M + 60
  ensures j * K == 38 * (M * M) + 60 * M
{
  assert j * K == M * K;
  assert M * K == M * (38 * M + 60);
}

import opened Prelude
