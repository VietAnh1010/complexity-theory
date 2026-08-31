// 633_A. Ebony and Ivory  (problem 1678, solution 1678_68)
// time complexity: O(1)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil
// def gcdEx(a,b,x,y):
//     if not a:
//         return 0,1,b
//     x1,y1,g=gcdEx(b%a,a,0,0)
//     x=y1-(b//a)*x1
//     y=x1
//     return x,y,g
// a,b,c=map(int, input().split())
// x,y,g=gcdEx(a,b,0,0)
// if c%g:
//     print("No")
// else:    
//     x,y=x*c//g,y*c//g
//     k1=ceil(-x*g/b)
//     k2=(y*g)//a
//     c=abs(k2-k1+1)
//     print("Yes" if c>0 else "No")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(rows: int, columns: int, value: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
