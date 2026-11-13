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

method Solve(m: int, n: int, edges: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |edges| ==> |edges[k]| >= 2
  requires |edges| == m && 1 <= n <= m
  ensures steps <= m * (12 * m + 20) + 6 * m + 30 + |output|
{
  steps := 2 * m + 2;
  var A: seq<(int, int)> := [(0, 0)] + ToPairs1671a(edges);
  var j := 2;
  ghost var base := steps;
  ghost var K := 12 * m + 20;
  while j <= m
    invariant |A| == m + 1
    invariant 2 <= j <= m + 1 || (m < 2 && j == 2)
    invariant steps <= base + (j - 2) * K
    decreases m + 1 - j
  {
    ghost var s0 := steps;
    steps := steps + 4;
    var key := A[j];
    var i := j - 1;
    while i > 0 && (A[i].0 > key.0 || (A[i].0 == key.0 && A[i].1 < key.1))
      invariant 0 <= i <= j - 1
      invariant |A| == m + 1
      invariant steps <= s0 + 4 + 12 * (j - 1 - i)
      decreases i
    {
      steps := steps + 12;
      A := A[i + 1 := A[i]];
      i := i - 1;
    }
    steps := steps + 12;
    A := A[i + 1 := key];
    j := j + 1;
    CostMulDistrib(j - 3, 1, j - 2, K);
  }
  CostMulMonoLeft(j - 2, m, K);
  steps := steps + 1;
  A := A[1..];
  var rev: seq<(int, int)> := [];
  var r := |A| - 1;
  ghost var s1 := steps;
  while r >= 0
    invariant -1 <= r < |A|
    invariant |A| == m
    invariant |rev| == |A| - 1 - r
    invariant steps <= s1 + 5 * (m - 1 - r)
    decreases r + 1
  {
    steps := steps + 5;
    rev := rev + [A[r]];
    r := r - 1;
  }
  steps := steps + m + 1;
  var B := [(0, 0)] + rev;
  steps := steps + |B|;
  var cnt := CountPair1671a(B, B[n]);
  IntToStringDigits(cnt);
  steps := steps + Digits(cnt);
  output := IntToString(cnt);
}
