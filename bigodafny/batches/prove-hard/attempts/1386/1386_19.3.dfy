// --- Python ---------------------------------------------------------
// import math
// n = int(input())
// arr = sorted(list(map(int, input().split())))
// b = 0
// for i in arr:
//     b = math.gcd(b, i)
// c = (arr[0] - 1) // b
// c += sum([(arr[i+1] - arr[i] - 1) // b for i in range(n-1)])
// print('Bob' if c % 2 == 0 else 'Alice')
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

lemma GcdPos(x: int, y: int)
  requires x >= 0 && y >= 0 && (x > 0 || y > 0)
  ensures Gcd(x, y) > 0
  decreases y
{
  if y == 0 {
  } else {
    GcdPos(y, x % y);
  }
}

method Solve(a: int, b_list: seq<int>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|b_list|) + a * (2 * CeilLog2(MaxSeq(b_list) + 1) + 6) + 12 * a + 10
  requires 1 <= a <= |b_list|
  requires forall k :: 0 <= k < |b_list| ==> b_list[k] >= 1
{
  steps := 0;
  var n := a;
  steps := steps + SortCost(|b_list|);
  var arr := SortInts(b_list);
  SortIntsKeepsElems(b_list);
  assert forall k :: 0 <= k < |arr| ==> arr[k] >= 1 by {
    forall k | 0 <= k < |arr|
      ensures arr[k] >= 1
    {
      assert arr[k] in arr;
      assert arr[k] in b_list;
      var j :| 0 <= j < |b_list| && b_list[j] == arr[k];
    }
  }
  SortCostWithin(|b_list|, |b_list|);
  ghost var M := MaxSeq(b_list);
  MaxSeqBound(b_list);
  assert forall k :: 0 <= k < |arr| ==> arr[k] <= M by {
    forall k | 0 <= k < |arr|
      ensures arr[k] <= M
    {
      assert arr[k] in b_list;
    }
  }
  ghost var K := 2 * CeilLog2(M + 1) + 6;
  var g := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant g >= 0
    invariant i > 0 ==> g > 0
    invariant steps <= 2 * NLogN(|b_list|) + 1 + i * K
    decreases n - i
  {
    steps := steps + 2;
    GcdPos(g, arr[i]);
    steps := steps + (1 + GcdSteps(g, arr[i]));
    GcdStepsBound(g, arr[i]);
    CeilLog2Monotone(arr[i] + 1, M + 1);
    CostMulDistrib(i, 1, i + 1, K);
    g := Gcd(g, arr[i]);
    steps := steps + 1;
    i := i + 1;
  }
  assert i == n;
  assert i * K == n * K;
  steps := steps + 1;
  steps := steps + (2 + 1);
  var c := FloorDiv(arr[0] - 1, g);
  i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant steps <= 2 * NLogN(|b_list|) + 1 + n * K + 4 + 12 * i
    decreases n - 1 - i
  {
    steps := steps + 3;
    steps := steps + (6 + 1);
    c := c + FloorDiv(arr[i + 1] - arr[i] - 1, g);
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 2;
  steps := steps + (2 + 1);
  output := if FloorMod(c, 2) == 0 then "Bob" else "Alice";
}

import opened Prelude
