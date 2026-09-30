// VALUE-BOUNDED -- filed for review; the proof carries a term the label omits.
//
//   This proof's bound depends on the MAGNITUDE of an input, not only on how
//   many inputs there are. BigOBench fitted the label by profiling, which
//   treats a capped value as constant; COMPLEXITY.md section 1 decides the
//   opposite, so the two disagree here by construction.
//
//   See solutions-proved/value-bounded/README.md for the category and
//   MANIFEST.jsonl for this row's entry.
//
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

include "../../../prelude.dfy"
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
// bounded O(k log k) by SortCostNLogN. Each Gcd call costs Euclid's
// recursion depth, GcdSteps, at most 2 * log(max + 1) + 2 (GcdStepsBound).

method Solve(a: int, b_list: seq<int>) returns (output: string, ghost steps: nat)
  requires 1 <= a <= |b_list|
  requires forall k :: 0 <= k < |b_list| ==> b_list[k] >= 1
  ensures steps <= 2 * |b_list| * (CeilLog2(|b_list|) + 1) + 5 * a
                 + 2 * a * BitLen(MaxSeq(b_list)) + 6
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
  ghost var L := BitLen(MaxSeq(b_list));
  MaxSeqBound(b_list);
  while i < n
    invariant 0 <= i <= n
    invariant g >= 0
    invariant i > 0 ==> g > 0
    invariant steps <= base1 + 3 * i + 2 * i * L
    decreases n - i
  {
    GcdPos(g, arr[i]);
    assert arr[i] in arr;
    CeilLog2Monotone(arr[i] + 1, MaxSeq(b_list) + 1);
    GcdStepsBound(g, arr[i]);
    steps := steps + 1 + GcdSteps(g, arr[i]);
    g := Gcd(g, arr[i]);
    assert 2 * (i + 1) * L == 2 * i * L + 2 * L;
    i := i + 1;
  }
  assert steps <= base1 + 3 * n + 2 * n * L;
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
  assert steps <= (1 + SortCost(|b_list|)) + 3 * n + 2 * n * L + 2 + 2 * n + 2;
  assert SortCost(|b_list|) <= 2 * |b_list| * (CeilLog2(|b_list|) + 1) + 1;
}
