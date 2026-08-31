// 605_A. Sorting Railway Cars  (problem 1053, solution 1053_38)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// arr=list(map(int,input().split()))
// l=[n]*(n+1)
// for c in arr:
//  l[c]=l[c-1]-1
// print(min(l))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
