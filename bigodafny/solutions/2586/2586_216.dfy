// 546_B. Soldier and Badges  (problem 2586, solution 2586_216)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// ans=0
// s=sorted(list(map(int,input().split())))
// for i in range(1,n):
//     if s[i]<=s[i-1]:
//         ans+=s[i-1]-s[i]+1
//         s[i]=s[i-1]+1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
