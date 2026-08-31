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

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
