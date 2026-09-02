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

method Log2Floor(x: int) returns (k: int)
  requires x >= 1
  ensures 0 <= k <= x
  ensures x >= 2 ==> k >= 1
{
  k := 0;
  var p := 1;
  while p * 2 <= x
    invariant p >= 1
    invariant p <= x
    invariant k <= p
    invariant (k == 0) == (p == 1)
    decreases x - p
  {
    p := p * 2;
    k := k + 1;
  }
}

method Solve(a: int, b: int, c: int) returns (output: string)
  requires a >= 1
{
  var nn := a;
  var matchesCount := 0;
  while nn > 1
    invariant nn >= 0
    decreases nn
  {
    var power := Log2Floor(nn);
    matchesCount := matchesCount + power;
    nn := nn - power;
  }
  var bottles := matchesCount * (2 * b + 1);
  var towels := a * c;
  output := IntToString(bottles) + " " + IntToString(towels);
}
