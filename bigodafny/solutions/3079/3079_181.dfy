// p03776 AtCoder Beginner Contest 057 - Maximum Average Sets  (problem 3079, solution 3079_181)
// time complexity: O(n**2)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import collections
// from math import factorial
// def comb(n,r):
//     return factorial(n)//factorial(n-r)//factorial(r)
// n,a,b=map(int,input().split())
// v=list(map(int,input().split()))
// v.sort(reverse=True)
// c=collections.Counter(v)
// k=min(v[:a])
// if c[max(v)]<a:
//     ans=comb(c[k],v[:a].count(k))
// else:
//     ans=0
//     for i in range(a,min(b,c[k])+1):
//         ans+=comb(c[k],i)
// print(sum(v[:a])/a)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, d: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
