// 219_A. k-String  (problem 1582, solution 1582_118)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def solve():
//     n=int(input())
//     s=sorted(input(), key=(lambda x: ord(x)))
//     ind=[[s[0],1]]
//     if len(s) % n!=0:
//         print(-1)
//         return
//     for i in range(1,len(s)):
//         if s[i]!=ind[len(ind)-1][0]:
//             ind.append([s[i],1])
//         else: ind[len(ind)-1][1]+=1
//     ans=[]
//     for ii in ind:
//         if ii[1] % n!=0:
//             print(-1)
//             return
//         ans.extend([ii[0] for i in range(ii[1]//n)])
//     print("".join(ans * n))
// solve()
// 
// 
//           
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
