// 127_B. Canvas Frames  (problem 659, solution 659_33)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// m=list(map(int,input().split()))
// k=set(m)
// k=list(k)
// c=0
// for i in k:
// 	c+=m.count(i)//2
// print(c//2)	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, ratings: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
