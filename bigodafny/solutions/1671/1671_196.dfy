// 166_A. Rank List  (problem 1671, solution 1671_196)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// A=[[0,0]]
// for i in range(n):
//     a,b=map(int,input().split())
//     A.append([a,b])
// for j in range(2,n+1):
//     key=A[j]
//     i=j-1
//     while(i>0 and (A[i][0]>key[0] or (A[i][0]==key[0] and A[i][1]<key[1]))):
//         A[i+1]=A[i]
//         i-=1
//     A[i+1]=key
// A.pop(0)
// A=[[0,0]]+A[::-1]
// print(A.count(A[k]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ToPairs1671a(edges: seq<seq<int>>): seq<(int, int)>
  decreases |edges|
{
  if |edges| == 0 then []
  else [(edges[0][0], edges[0][1])] + ToPairs1671a(edges[1..])
}

function CountPair1671a(xs: seq<(int, int)>, t: (int, int)): int
  decreases |xs|
{
  if |xs| == 0 then 0
  else (if xs[0] == t then 1 else 0) + CountPair1671a(xs[1..], t)
}

method Solve(m: int, n: int, edges: seq<seq<int>>) returns (output: string)
{
  var pairs := ToPairs1671a(edges);
  var asc := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 > y.1));
  var target := asc[m - n];
  var cnt := CountPair1671a(pairs, target);
  output := IntToString(cnt);
}
