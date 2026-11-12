// 389_A. Fox and Number Game  (problem 281, solution 281_250)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #CF389A
// n,q=int(input()),0
// import math 
// for i in map(int,input().split()):q=math.gcd(q,i)
// print(q*n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires forall x :: x in a_list ==> x >= 0
{
  var q := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i
    invariant q >= 0
    decreases |a_list| - i
  {
    assert a_list[i] in a_list;
    q := Gcd(q, a_list[i]);
    i := i + 1;
  }
  output := IntToString(q * n);
}

function Gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures Gcd(a, b) >= 0
  decreases b
{
  if b == 0 then a else Gcd(b, a % b)
}
