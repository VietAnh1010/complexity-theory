// 127_B. Canvas Frames  (problem 659, solution 659_33)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// m=list(map(int,input().split()))
// k=set(m)
// k=list(k)
// c=0
// for i in k:
// 	c+=m.count(i)//2
// print(c//2)	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, ratings: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 6 * (|ratings| * |ratings|) + 30 * |ratings| + 20 + |output|
{
  steps := 1;
  ghost var N: nat := |ratings|;
  ghost var K1: nat := N + 10;
  ghost var K2: nat := 5 * N + 12;
  var distinct: seq<int> := [];
  var i := 0;
  while i < |ratings|
    invariant 0 <= i <= |ratings|
    invariant |distinct| <= i
    invariant steps <= 1 + i * K1
    decreases |ratings| - i
  {
    CostMulDistrib(i, 1, i + 1, K1);
    steps := steps + 1 + 1 + 1 + |distinct| + 1 + 1 + 1;
    if ratings[i] !in distinct {
      distinct := distinct + [ratings[i]];
    }
    i := i + 1;
  }
  CostMulMonoLeft(i, N, K1);
  var c := 0;
  i := 0;
  steps := steps + 1;
  ghost var base := steps;
  while i < |distinct|
    invariant 0 <= i <= |distinct|
    invariant |distinct| <= |ratings|
    invariant steps <= base + i * K2
    decreases |distinct| - i
  {
    var cnt, st := CountOccurrences659(ratings, distinct[i]);
    CostMulDistrib(i, 1, i + 1, K2);
    steps := steps + st + 6;
    c := c + cnt / 2;
    i := i + 1;
  }
  CostMulMonoLeft(i, N, K2);
  output := IntToString(c / 2);
  IntToStringDigits(c / 2);
  steps := steps + Digits(c / 2) + 2;
  assert N * K1 == N * N + 10 * N;
  assert N * K2 == 5 * (N * N) + 12 * N;
}

method CountOccurrences659(xs: seq<int>, v: int) returns (cnt: int, ghost steps: nat)
  ensures steps <= 5 * |xs| + 2
{
  steps := 1;
  cnt := 0;
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant steps == 1 + 5 * i
    decreases |xs| - i
  {
    if xs[i] == v { cnt := cnt + 1; }
    i := i + 1;
    steps := steps + 5;
  }
  steps := steps + 1;
}
