// 281_B. Nearest Fraction  (problem 696, solution 696_51)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import inf,floor,ceil
// x,y,n=map(float,input().split())
// m=inf
// ans=""
// for b in range(1,int(n+1)):
//     a=floor((x*b)/y)
//     z=abs(x/y-a/b)
//     if z<m-1e-15:
//         m=z
//         ans=str(a)+'/'+str(b)
//     a=ceil((x*b)/y)
//     z=abs(x/y-a/b)
//     if z<m-1e-15:
//         m=z
//         ans=str(a)+'/'+str(b)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: int, v_2: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
