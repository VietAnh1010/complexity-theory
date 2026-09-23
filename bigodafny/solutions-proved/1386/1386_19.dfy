// 346_A. Alice and Bob  (problem 1386, solution 1386_19)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

include "../../prelude.dfy"
import opened Prelude

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

// Sort dominates: the two post-sort passes are each linear. Following the
// precedent in solutions-proved/1871/1871_156.dfy, Sort's own cost is
// charged via the standard T(k) = T(k/2) + T(k-k/2) + k recurrence and
// bounded O(k log k) by SortCostNLogN. Gcd is charged 1 per call, an
// opaque unit-cost primitive (not a seq/string recursion).

method Solve(a: int, b_list: seq<int>) returns (output: string, ghost steps: nat)
  requires 1 <= a <= |b_list|
  requires forall k :: 0 <= k < |b_list| ==> b_list[k] >= 1
  ensures steps <= 2 * |b_list| * (CeilLog2(|b_list|) + 1) + 6 * |b_list| + 12
{
  var n := a;
  var arr := SortInts(b_list);
  SortIntsKeepsElems(b_list);
  SortCostTreeBound(|b_list|);
  steps := 1 + SortCost(|b_list|);
  assert forall k :: 0 <= k < |arr| ==> arr[k] >= 1 by {
    forall k | 0 <= k < |arr|
      ensures arr[k] >= 1
    {
      assert arr[k] in arr;
      assert arr[k] in b_list;
      var j :| 0 <= j < |b_list| && b_list[j] == arr[k];
    }
  }
  var g := 0;
  var i := 0;
  ghost var base1 := steps;
  while i < n
    invariant 0 <= i <= n
    invariant g >= 0
    invariant i > 0 ==> g > 0
    invariant steps <= base1 + 2 * i
    decreases n - i
  {
    GcdPos(g, arr[i]);
    g := Gcd(g, arr[i]);
    i := i + 1;
    steps := steps + 2;
  }
  assert steps <= base1 + 2 * n;
  var c := FloorDiv(arr[0] - 1, g);
  steps := steps + 2;
  i := 0;
  ghost var base2 := steps;
  while i < n - 1
    invariant 0 <= i <= n
    invariant steps <= base2 + 2 * i
    decreases n - 1 - i
  {
    c := c + FloorDiv(arr[i+1] - arr[i] - 1, g);
    i := i + 1;
    steps := steps + 2;
  }
  assert steps <= base2 + 2 * n;
  output := if FloorMod(c, 2) == 0 then "Bob" else "Alice";
  steps := steps + 2;
  assert n <= |b_list|;
  assert steps <= (1 + SortCost(|b_list|)) + 2 * n + 2 + 2 * n + 2;
  assert SortCost(|b_list|) <= 2 * |b_list| * (CeilLog2(|b_list|) + 1) + 1;
}
