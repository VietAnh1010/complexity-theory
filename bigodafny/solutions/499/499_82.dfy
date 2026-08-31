// 1206_B. Make Product Equal One  (problem 499, solution 499_82)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// a.sort()
// ans=0
// for i in range(0,n-1,2):
//     ans+=min(abs(-1-a[i+1])+abs(-1-a[i]),abs(1-a[i+1])+abs(1-a[i]))
// if (n%2==1): ans+=abs(1-a[n-1])
// print(ans)
//     
//     
//     
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
