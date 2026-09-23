// p03948 AtCoder Regular Contest 063 - An Invisible Hand  (problem 2051, solution 2051_25)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// (N,T)=map(int,input().split())
// a=list(map(int,input().split()))
// x=10**9
// d=0
// counter=0
// for i in a:
//     if i<x:
//         x=i
//     elif i-x>d:
//         d=i-x
//         counter=1
//     elif i-x==d:
//         counter+=1
// print(counter)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * |numbers| + 2
{
  var a := numbers;
  var x := 1000000000;
  var d := 0;
  var counter := 0;
  var idx := 0;
  steps := 1;
  while idx < |a|
    invariant 0 <= idx <= |a|
    invariant steps <= 1 + 4 * idx
    decreases |a| - idx
  {
    var i := a[idx];
    if i < x {
      x := i;
    } else if i - x > d {
      d := i - x;
      counter := 1;
    } else if i - x == d {
      counter := counter + 1;
    }
    idx := idx + 1;
    steps := steps + 4;
  }
  output := IntToString(counter);
  steps := steps + 1;
}
