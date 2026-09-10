// 354_95 (problem 354) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(nlogn)
//   proved bound    : a * (2 * CeilLog2(a) + 5) + 10
//   proved class    : O(nlogn)
//   agent verdict   : proves
//   reference label : O(n)
//   prediction correct against the label: False
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     outer while(nn>1) runs O(n) times (nn drops by >=1 each round since
//     power>=1); each round calls Log2Floor(nn), whose own loop doubles p so
//     runs O(log n) times
//
//   agent notes:
//     Added ghost steps to Log2Floor (bounded 2*CeilLog2(x)+3, via
//     Pow2/CeilLog2 relation lemma) and to Solve (bounded a*K+1 via a loop
//     invariant, K=2*CeilLog2(a)+5, using CeilLog2 monotonicity since nn<=a
//     always). Needed to isolate the (a-nn)*K multiplication into two tiny
//     lemmas (distribute, monotone-in-left-arg) per GUIDE.md's
//     nonlinear-arithmetic advice; verified on first try after that.
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 354_95
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
// #!/usr/bin/env python3
// # -*- coding: utf-8 -*-
// """
// Created on Sun Jun 28 10:54:09 2020
// 
// @author: shailesh
// """
// import math
// 
// n,b,p = [int(i) for i in input().split()]
// matches_count = 0
// towels = n*p
// while(n>1):
//     power = int(math.log2(n))
//     matches_count += power
//     n = n - power
// 
// bottles = matches_count*(2*b + 1)
// print(bottles,towels)
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function Pow2(k: nat): nat
  decreases k
{
  if k == 0 then 1 else 2 * Pow2(k - 1)
}

ghost function CeilLog2(n: nat): nat
  decreases n
{
  if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2)
}

lemma Pow2Pos(k: nat)
  ensures Pow2(k) >= 1
  decreases k
{
  if k == 0 {
  } else {
    Pow2Pos(k - 1);
  }
}

lemma Pow2CeilLog2Lemma(k: nat, x: nat)
  requires x >= 1
  requires Pow2(k) <= x
  ensures k <= CeilLog2(x)
  decreases k
{
  if k == 0 {
  } else {
    Pow2Pos(k - 1);
    assert Pow2(k) == 2 * Pow2(k - 1);
    assert x >= 2;
    assert Pow2(k - 1) <= x / 2;
    assert x / 2 <= (x + 1) / 2;
    Pow2CeilLog2Lemma(k - 1, (x + 1) / 2);
  }
}

lemma CeilLog2Monotonic(x: nat, y: nat)
  requires 1 <= x <= y
  ensures CeilLog2(x) <= CeilLog2(y)
  decreases y
{
  if x <= 1 {
  } else {
    assert CeilLog2(x) == 1 + CeilLog2((x + 1) / 2);
    assert CeilLog2(y) == 1 + CeilLog2((y + 1) / 2);
    assert (x + 1) / 2 <= (y + 1) / 2;
    CeilLog2Monotonic((x + 1) / 2, (y + 1) / 2);
  }
}

method Log2Floor(x: int) returns (k: int, ghost steps: nat)
  requires x >= 1
  ensures 0 <= k <= x
  ensures x >= 2 ==> k >= 1
  ensures steps <= 2 * CeilLog2(x) + 3
{
  k := 0;
  var p := 1;
  steps := 1;
  while p * 2 <= x
    invariant p >= 1
    invariant p <= x
    invariant k >= 0
    invariant k <= p
    invariant (k == 0) == (p == 1)
    invariant p == Pow2(k)
    invariant steps == 2 * k + 1
    decreases x - p
  {
    p := p * 2;
    k := k + 1;
    steps := steps + 2;
  }
  Pow2CeilLog2Lemma(k, x);
}

lemma MulDistribAdd1(m: int, K: int)
  ensures (m + 1) * K == m * K + K
{}

lemma MulMonoLeft(p: int, q: int, K: int)
  requires p <= q
  requires K >= 0
  ensures p * K <= q * K
{}

method Solve(a: int, b: int, c: int) returns (output: string, ghost steps: nat)
  requires a >= 1
  ensures steps <= a * (2 * CeilLog2(a) + 5) + 10
{
  var nn := a;
  var matchesCount := 0;
  steps := 1;
  ghost var K := 2 * CeilLog2(a) + 5;
  while nn > 1
    invariant 0 <= nn <= a
    invariant steps <= (a - nn) * K + 1
    decreases nn
  {
    ghost var oldNn := nn;
    var power, hSteps := Log2Floor(nn);
    CeilLog2Monotonic(nn, a);
    assert hSteps <= K - 2;
    matchesCount := matchesCount + power;
    nn := nn - power;
    steps := steps + hSteps + 2;
    MulDistribAdd1(a - oldNn, K);
    MulMonoLeft(a - oldNn + 1, a - nn, K);
  }
  var bottles := matchesCount * (2 * b + 1);
  var towels := a * c;
  output := IntToString(bottles) + " " + IntToString(towels);
  steps := steps + 3;
}
