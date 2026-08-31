// 1102_C. Doors Breaking and Repairing  (problem 2982, solution 2982_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x,y=input().split()
// n=int(n)
// x=int(x)
// y=int(y)
// 
// l=[int(x) for x in input().split()]
// 
// l.sort()
// 
// count_a=0
// 
// 
// for i in range(n):
// 	if(l[i]<=x):
// 		count_a+=1
// 
// if(x>y):
// 	print(n)
// 
// else:
// 	print((count_a%2)+(count_a//2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
