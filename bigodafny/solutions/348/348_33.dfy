// 24_A. Ring road  (problem 348, solution 348_33)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys,math
// n=int(sys.stdin.readline())
// start =[]
// end=[]
// ans1=0
// ans2=0
// for i in range(n):
//     a,b,c=map(int,sys.stdin.readline().split())
//     if (a in start) or (b in end):
//         ans1+=c
//         start.append(b)
//         end.append(a)
//     else:
//         ans2+=c 
//         start.append(a)
//         end.append(b)
// print(min(ans1,ans2))        
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, v_list: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
