// 158_B. Taxi  (problem 223, solution 223_3085)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = list(map(int, input().split()))
//
// s.sort()
//
// i, j = 0, len(s)-1
// res = 0
//
// while i<j:
//     if s[i]+s[j]<=4:
//         s[j] += s[i]
//         i += 1
//     else:
//         j -= 1
//         res += 1
//
// print(res+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
// Prelude.Sort/SortInts is a plain recursive function (merge sort); it carries
// no ghost step counter (prelude.dfy is off limits), so its cost is charged
// as an opaque-but-defined SortCost mirroring Sort's own split. The bound
// proved here is an honest O(k^2) -- weaker than merge sort's true O(k log k)
// -- so this is the loose scaffold, not the tight recursion-tree argument.
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

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |a_list| * |a_list| + 5 * |a_list| + 5
{
  SortCostBound(|a_list|);
  steps := 1 + SortCost(|a_list|);
  var s := SortInts(a_list);
  var i := 0;
  var j := |s| - 1;
  var res := 0;
  while i < j
    invariant 0 <= i
    invariant j < |s|
    invariant i <= j + 1
    invariant |s| == |a_list|
    invariant steps <= 1 + SortCost(|a_list|) + 2 * (i + (|s| - 1 - j))
    decreases j - i
  {
    if s[i] + s[j] <= 4 {
      s := s[j := s[j] + s[i]];
      i := i + 1;
    } else {
      j := j - 1;
      res := res + 1;
    }
    steps := steps + 2;
  }
  assert |s| == |a_list|;
  assert i >= j;
  assert i + (|s| - 1 - j) <= |a_list|;
  assert steps <= 1 + SortCost(|a_list|) + 2 * |a_list|;
  output := IntToString(res + 1);
  steps := steps + 2;
}
