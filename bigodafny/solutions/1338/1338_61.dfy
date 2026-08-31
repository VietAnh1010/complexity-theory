// 1261_B1. Optimal Subsequences (Easy Version)  (problem 1338, solution 1338_61)
// time complexity: O(n*m)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import copy
// a=[]
// ai=[]
// otv=''
// n=int(input())
// a=list(map(int,input().split()))
// m=int(input())
// for i in range(1,m+1):
//     #print(ai)
//     #print(a,'kkkk')
//     ai=copy.deepcopy(a)
//     ai.reverse()
//     #print(ai)
//     k,pos=map(int,input().split())
//     for j in range(1,n-k+1):
//         #print(min(ai))
//         ai.remove(min(ai))
//     ai.reverse()
//     otv=otv+'\n'+str(ai[pos-1])
// print(otv)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, q: int, queries: seq<(int, int)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
