// 440_A. Forgotten Episode  (problem 2742, solution 2742_0)
// time complexity: O(nlogn)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input=sys.stdin.buffer.readline
//
// n=int(input())
// arr=list(map(int,input().split()))
// arr.sort()
// z=0
// for i in range(0,n-1):
// 	if arr[i]==i+1:
// 		continue
// 	else:
// 		print(i+1)
// 		z=1
// 		break
// if z==0:
// 	print(n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
// Same SortCost scaffold as elsewhere: an honest O(k^2) bound on Sort,
// weaker than merge sort's true O(k log k).
ghost function SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1
  else SortCost(k / 2) + SortCost(k - k / 2) + k
}

lemma SquareSplit(k: nat, L: nat)
  requires 2 * L <= k <= 2 * L + 1
  ensures 2 * L * L + 2 * (k - L) * (k - L) <= k * k + 1
{
  var d := k - 2 * L;
  assert d == 0 || d == 1;
  assert k - L == L + d;
  assert 2 * L * L + 2 * (k - L) * (k - L) == 4 * L * L + 4 * L * d + 2 * d * d;
  assert k == 2 * L + d;
  assert k * k == 4 * L * L + 4 * L * d + d * d;
  assert d * d <= 1;
}

lemma QuadTail(k: nat)
  requires k >= 2
  ensures k * k + k + 3 <= 2 * k * k + 1
{
  assert (k - 2) * (k + 1) >= 0;
}

lemma SortCostBound(k: nat)
  ensures SortCost(k) <= 2 * k * k + 1
  decreases k
{
  if k <= 1 {
  } else {
    var L := k / 2;
    var R := k - L;
    SortCostBound(L);
    SortCostBound(R);
    SquareSplit(k, L);
    assert SortCost(k) == SortCost(L) + SortCost(R) + k;
    assert SortCost(L) + SortCost(R) + k <= (2 * L * L + 1) + (2 * R * R + 1) + k;
    assert (2 * L * L + 1) + (2 * R * R + 1) + k == 2 * L * L + 2 * R * R + k + 2;
    assert 2 * L * L + 2 * R * R + k + 2 <= (k * k + 1) + k + 2;
    QuadTail(k);
  }
}

// Label O(nlogn) -- disagrees with the proof below, which only establishes
// O(n^2) (SortCost's honest bound; tight O(n log n) not attempted). The loop
// itself runs at most N-1 iterations, exiting early via z.
method Solve(N: int, values: seq<int>) returns (output: string, ghost steps: nat)
  requires N == |values|
  ensures steps <= 2 * |values| * |values| + 5 * |values| + 5
{
  SortCostBound(|values|);
  steps := 1 + SortCost(|values|);
  var arr := SortInts(values);
  assert |arr| == |values|;
  var z := 0;
  var i := 0;
  output := "";
  while i < N - 1 && z == 0
    invariant 0 <= i <= N
    invariant steps <= 1 + SortCost(|values|) + 2 * i + 2
    decreases (if N - 1 - i > 0 then N - 1 - i else 0)
  {
    if i < |arr| && arr[i] == i + 1 {
      // continue
    } else {
      output := IntToString(i + 1) + "\n";
      z := 1;
    }
    i := i + 1;
    steps := steps + 2;
  }
  if z == 0 {
    output := IntToString(N) + "\n";
  }
  steps := steps + 1;
}
