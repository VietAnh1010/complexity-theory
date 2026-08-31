// 1244_A. Pens and Pencils  (problem 89, solution 89_463)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// for i in range(n):
//    k=list(map(int,input().split()))
//    if k[0]%k[2]==0:
//      x=k[0]//k[2]
//    else:
//      x=k[0]//k[2]+1
//    if k[1]%k[3]==0:
//      y=k[1]//k[3]
//    else:
//      y=k[1]//k[3]+1
//    if (x+y)<=k[-1]:
//      print(x,y)
//    else:
//      print('-1')
//    
// 
// 
// 
// 
// 
// 
// 
//       
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
