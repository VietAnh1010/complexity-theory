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
  var n := a;
  var x := b;
  var y := c;
  var l := SortInts(d_list);
  var countA := 0;
  var i := 0;
  while i < n
    invariant 0 <= i
    decreases n - i
  {
    if i < |l| && l[i] <= x { countA := countA + 1; }
    i := i + 1;
  }
  if x > y {
    output := IntToString(n);
  } else {
    output := IntToString((countA % 2) + (countA / 2));
  }
}
