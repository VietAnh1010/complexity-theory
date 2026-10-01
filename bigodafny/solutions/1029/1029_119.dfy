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


method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
  requires forall k :: 0 <= k < |a_list| ==> 0 <= a_list[k] < 0x1_0000_0000_0000_0000
  requires forall k :: 0 <= k < |b_list| ==> 0 <= b_list[k] < 0x1_0000_0000_0000_0000
{
  var f1 := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant 0 <= f1 < 0x1_0000_0000_0000_0000
    decreases |a_list| - i
  {
    f1 := BitOr(f1, a_list[i]);
    i := i + 1;
  }
  var f2 := 0;
  i := 0;
  while i < |b_list|
    invariant 0 <= i <= |b_list|
    invariant 0 <= f2 < 0x1_0000_0000_0000_0000
    decreases |b_list| - i
  {
    f2 := BitOr(f2, b_list[i]);
    i := i + 1;
  }
  output := IntToString(f1 + f2);
}
