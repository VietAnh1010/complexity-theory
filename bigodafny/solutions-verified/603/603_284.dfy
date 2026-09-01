// 1041_A. Heist  (problem 603, solution 603_284)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=list(map(int,input().split()))
// l.sort()
// x=0
// for i in range(n-1):
//     x+=l[i+1]-l[i]-1
// print(x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
//
// Prelude.Sort is a plain recursive function (merge sort). We cannot attach a
// ghost step counter to it (it lives in prelude.dfy, off limits), so its cost
// is charged as an opaque-but-defined function SortCost, whose recursion
// mirrors Sort's own split (Sort(s) recurses on s[..|s|/2] and s[|s|/2..],
// then Merge is linear in the combined length). SortCostBound proves an
// honest, assumption-free O(k^2) bound on it -- weaker than the true
// O(k log k) of merge sort, but a real proof, not a guess.

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
  var d := k - 2 * L; // d is 0 or 1
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

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires |numbers| == n
  ensures steps <= 2 * n * n + 2 * n + 4
{
  SortCostBound(n);
  steps := 1 + SortCost(n);

  var l := SortInts(numbers);
  SortLength(numbers, (x, y) => x < y);
  assert |l| == n;

  var x := 0;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n
    invariant i < n - 1 ==> i + 1 < n
    invariant steps <= 1 + SortCost(n) + 2 * i
    decreases n - 1 - i
  {
    x := x + l[i+1] - l[i] - 1;
    i := i + 1;
    steps := steps + 2;
  }
  output := IntToString(x);
  assert steps <= 1 + SortCost(n) + 2 * n;
  assert SortCost(n) <= 2 * n * n + 1;
  steps := steps + 1;
}
