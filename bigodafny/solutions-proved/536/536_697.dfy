// 451_A. Game With Sticks  (problem 536, solution 536_697)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #!/usr/bin/env python3
// # -*- coding: utf-8 -*-
// """
// Created on Mon Apr 10 15:10:38 2017
// 
// @author: lawrenceylong
// """
// 
// answer = min(map(int,input().split()))
// print("Malvika") if answer%2 == 0 else print("Akshat")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= 5
{
  steps := 0;
  var m := if a <= b then a else b;
  steps := steps + 2;
  if m % 2 == 0 {
    output := "Malvika";
  } else {
    output := "Akshat";
  }
  steps := steps + 2;
}
