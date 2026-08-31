// 525_B. Pasha and String  (problem 380, solution 380_112)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = list(input())
// m = int(input())
// n=len(s)
// lis = sorted(map(int,input().split()))
// has=[0]*(n+3)
// for i in range(m):
//     a=lis[i]
//     has[a-1]+=1
// for i in range(1,n+2):
//     has[i]+=has[i-1]       
// for i in range(n//2):
//     if has[i]%2:
//         s[i],s[n-i-1]=s[n-i-1],s[i]
// print(''.join(s))               
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string, n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
