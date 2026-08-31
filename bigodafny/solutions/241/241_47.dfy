// 1038_D. Slime  (problem 241, solution 241_47)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// if n==1:
//     print(a[0])
// elif all(ele>0 for ele in a):
//     s=sum(a)-2*min(a) 
//     print(s)
// elif all(ele<0 for ele in a):
//     s=abs(sum(a))-2*abs(max(a))
//     print(s)
// else:
//     ans=0 
//     for ele in a:
//         ans+=abs(ele)
//     print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
