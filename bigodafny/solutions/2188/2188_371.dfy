// 1365_C. Rotation Matching  (problem 2188, solution 2188_371)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// b=list(map(int,input().split()))
// ga={}
// gb={}
// for i in range(n):ga[a[i]]=i;gb[b[i]]=i
// g={}
// for i in range(1,n+1):o=(gb[i]-ga[i])%n;g[o]=g[o]+1if g.get(o)else 1
// print(max(g[i]for i in g))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
