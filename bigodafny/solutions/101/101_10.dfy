// 814_A. An abandoned sentiment from past  (problem 101, solution 101_10)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=map(int,input().split())
// l=list(map(int,input().split()))
// k=list(sorted(map(int,input().split()),reverse=True))
// for i in range(n):
//     if l[i]==0:
//         l[i]=k[0]
//         k.pop(0)
// if l==sorted(l):
//     print("No")
// else:
//     print("Yes")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
