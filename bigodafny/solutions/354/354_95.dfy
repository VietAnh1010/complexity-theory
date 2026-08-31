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

method Solve(a: int, b: int, c: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
