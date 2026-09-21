// 628_A. Tennis Tournament  (problem 354, solution 354_95)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
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
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Log2Floor(x: int) returns (k: int, ghost steps: nat)
  requires x >= 1
  ensures 0 <= k <= x
  ensures x >= 2 ==> k >= 1
  ensures steps <= 3 * k + 3
{
  steps := 2;
  k := 0;
  var p := 1;
  while p * 2 <= x
    invariant p >= 1
    invariant p <= x
    invariant k <= p
    invariant (k == 0) == (p == 1)
    invariant steps <= 3 * k + 2
    decreases x - p
  {
    p := p * 2;
    k := k + 1;
    steps := steps + 3;
  }
}

method Solve(a: int, b: int, c: int) returns (output: string, ghost steps: nat)
  requires a >= 1
  ensures steps <= 9 * a + 10
{
  steps := 1;
  var nn := a;
  var matchesCount := 0;
  while nn > 1
    invariant 0 <= nn <= a
    invariant steps <= 9 * (a - nn) + 1
    decreases nn
  {
    var power, s2 := Log2Floor(nn);
    matchesCount := matchesCount + power;
    nn := nn - power;
    steps := steps + s2 + 2;
  }
  var bottles := matchesCount * (2 * b + 1);
  var towels := a * c;
  steps := steps + 3;
  output := IntToString(bottles) + " " + IntToString(towels);
  steps := steps + 3;
}
