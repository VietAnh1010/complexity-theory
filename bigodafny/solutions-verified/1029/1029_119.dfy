// 631_A. Interview  (problem 1029, solution 1029_119)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// f1=f2=0
// for x in input().split(): f1|=int(x)
// for x in input().split(): f2|=int(x)
// print(f1+f2)
//   
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function BitOr(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a + b
  ensures BitOr(a, b) >= 0
{
  if a == 0 then b
  else if b == 0 then a
  else 2 * BitOr(a / 2, b / 2) + (if a % 2 == 1 || b % 2 == 1 then 1 else 0)
}


method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string, ghost steps: nat)
  requires forall i :: 0 <= i < |a_list| ==> a_list[i] >= 0
  requires forall i :: 0 <= i < |b_list| ==> b_list[i] >= 0
  ensures steps <= 2 * |a_list| + 2 * |b_list| + 3
{
  steps := 1;
  var f1 := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant f1 >= 0
    invariant steps == 2 * i + 1
    decreases |a_list| - i
  {
    f1 := BitOr(f1, a_list[i]);
    i := i + 1;
    steps := steps + 2;
  }
  var f2 := 0;
  i := 0;
  while i < |b_list|
    invariant 0 <= i <= |b_list|
    invariant f2 >= 0
    invariant steps == 2 * |a_list| + 2 * i + 1
    decreases |b_list| - i
  {
    f2 := BitOr(f2, b_list[i]);
    i := i + 1;
    steps := steps + 2;
  }
  output := IntToString(f1 + f2);
  steps := steps + 1;
}
