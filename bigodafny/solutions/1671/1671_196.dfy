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
  requires forall k :: 0 <= k < |edges| ==> |edges[k]| >= 2
  ensures |ToPairs1671a(edges)| == |edges|
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
  requires forall k :: 0 <= k < |edges| ==> |edges[k]| >= 2
  requires |edges| == m && 1 <= n <= m
{
  var A: seq<(int, int)> := [(0, 0)] + ToPairs1671a(edges);
  var j := 2;
  while j <= m
    invariant |A| == m + 1
    decreases m + 1 - j
  {
    var key := A[j];
    var i := j - 1;
    while i > 0 && (A[i].0 > key.0 || (A[i].0 == key.0 && A[i].1 < key.1))
      invariant 0 <= i <= j - 1
      invariant |A| == m + 1
      decreases i
    {
      A := A[i + 1 := A[i]];
      i := i - 1;
    }
    A := A[i + 1 := key];
    j := j + 1;
  }
  A := A[1..];
  var rev: seq<(int, int)> := [];
  var r := |A| - 1;
  while r >= 0
    invariant -1 <= r < |A|
    invariant |rev| == |A| - 1 - r
    decreases r + 1
  {
    rev := rev + [A[r]];
    r := r - 1;
  }
  var B := [(0, 0)] + rev;
  var cnt := CountPair1671a(B, B[n]);
  output := IntToString(cnt);
}
