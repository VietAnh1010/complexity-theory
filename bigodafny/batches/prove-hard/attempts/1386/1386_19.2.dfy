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

lemma SortHeadLe(s: seq<int>)
  requires |s| >= 1
  ensures SortInts(s)[0] <= s[0]
{
  SortIntsIsSorted(s);
  SortIntsKeepsElems(s);
  assert s[0] in SortInts(s);
  var j0 :| 0 <= j0 < |SortInts(s)| && SortInts(s)[j0] == s[0];
  if j0 > 0 { assert !(SortInts(s)[j0] < SortInts(s)[0]); }
}

method Solve(a: int, b_list: seq<int>)
    returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|b_list|) + a * (2 * CeilLog2(b_list[0] + 1) + 7) + 11 * a + 10
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
  SortIntsIsSorted(b_list);
  SortCostWithin(|b_list|, |b_list|);
  SortHeadLe(b_list);
  ghost var L := CeilLog2(b_list[0] + 1);
  ghost var K := 2 * L + 7;
  CeilLog2Monotone(arr[0] + 1, b_list[0] + 1);
  ghost var S0 := 2 * NLogN(|b_list|) + 1;
  var g := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= S0 + i * K
    invariant g <= arr[0]
    invariant g >= 0
    invariant i > 0 ==> g > 0
    decreases n - i
  {
    GcdPos(g, arr[i]);
    GcdStepsBoundFirst(g, arr[i]);
    if i == 0 { GcdLeSecond(g, arr[i]); } else { GcdLeFirst(g, arr[i]); }
    CeilLog2Monotone(g + 1, arr[0] + 1);
    CeilLog2Monotone(arr[0] + 1, b_list[0] + 1);
    CostMulDistrib(i, 1, i + 1, K);
    steps := steps + 2;
    steps := steps + (1 + GcdSteps(g, arr[i]));
    g := Gcd(g, arr[i]);
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  steps := steps + (2 + 1);
  var c := FloorDiv(arr[0] - 1, g);
  i := 0;
  ghost var S1 := steps;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant steps <= S1 + 11 * i
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
