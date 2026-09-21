// 991_B. Getting an A  (problem 2593, solution 2593_332)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// L = list(map(int, input().split()))
// L = sorted(L)
// s = sum(L)
// c = 0
// p = s/n
// if p >= 4.5:
//     print(0)
// else:
//     for i in range(n):
//         s = s-L[i]+5
//         c += 1
//         if s/n >= 4.5:
//             print(c)
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MergeLength<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
  ensures |Merge(a, b, less)| == |a| + |b|
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeLength(a, b[1..], less);
  } else {
    MergeLength(a[1..], b, less);
  }
}

lemma SortLength<T>(s: seq<T>, less: (T, T) -> bool)
  ensures |Sort(s, less)| == |s|
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortLength(s[..|s| / 2], less);
    SortLength(s[|s| / 2..], less);
    MergeLength(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

// Sort/Merge are plain recursive functions in prelude.dfy (off limits, so no
// ghost step counter can be attached there). Their cost is charged as an
// opaque-but-defined function SortCost, whose recursion mirrors Sort's own
// split. SortCostBound proves a quadratic bound on it -- looser than the
// true O(k log k), which is the tight bound proved elsewhere in this corpus
// (solutions-proved/nlogn/) via a CeilLog2 recursion-tree argument. Given the
// per-row attempt/time budget, this copy keeps the simpler quadratic
// scaffold: relation looser-slack.
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
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 2 * n * n + 2 * n + 4
{
  SortLength(a_list, (x: int, y: int) => x < y);
  SortCostBound(n);
  var l := SortInts(a_list);
  var s := SumSeq(l);
  steps := 1 + SortCost(n);
  if 2 * s >= 9 * n {
    output := "0";
  } else {
    var i := 0;
    var res := 0;
    var printed := false;
    while i < n && !printed
      invariant 0 <= i <= n
      invariant |l| == n
      invariant steps <= 1 + SortCost(n) + 2 * i
      decreases n - i
    {
      s := s - l[i] + 5;
      if 2 * s >= 9 * n {
        res := i + 1;
        printed := true;
      }
      i := i + 1;
      steps := steps + 2;
    }
    output := IntToString(res);
  }
  steps := steps + 1;
}
