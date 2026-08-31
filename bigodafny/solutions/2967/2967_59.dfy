// 399_A. Pages  (problem 2967, solution 2967_59)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,p,k=map(int,input().split(" "))
// ans=""
// if p-k>1:
//     ans+='<< '
// for i in range(p-k, p+k+1):
//     if i>0 and i<=n:
//         if i==p:
//             ans+='('+str(p)+') '
//         else:
//             ans+=str(i)+' '
// if p+k<n:
//     ans+='>>'
// if ans[len(ans)-1]==" ":
//     print(ans[0:len(ans)-1])
// else:
//     print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: string, v_1: string, v_2: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
