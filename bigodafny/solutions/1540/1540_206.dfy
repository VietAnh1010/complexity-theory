// 873_A. Chores  (problem 1540, solution 1540_206)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k,x=map(int,input().split())
// a=list(map(int,input().split()))
// a.sort(reverse=True)
// for i in range(0,k):
//     a[i]=x
// print(sum(a))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a: int, b: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
