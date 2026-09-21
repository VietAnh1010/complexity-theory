// 999_C. Alphabetic Removals  (problem 2725, solution 2725_319)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=list(map(int,input().split()))
// s=list(input())
// x=sorted([j,i] for i,j in enumerate(s))
// #print(x)
// for i in range(k):
//     s[x[i][1]]=''
// print(''.join(s))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
// Prelude.Sort is a plain recursive function (merge sort); it carries no
// ghost step counter (prelude.dfy is off limits), so its cost is charged as
// an opaque-but-defined SortCost mirroring Sort's own split. The bound proved
// here is an honest O(k^2) -- weaker than merge sort's true O(k log k) --
// so relation = looser-slack.
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

method Solve(n: int, k: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= SortCost(|s|) + 11 * |s| + 8
{
  steps := 1;
  var pairArr: seq<(char, int)> := seq(|s|, _ => (' ', 0));
  var i := 0;
  steps := steps + 1;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |pairArr| == |s|
    invariant steps <= 3 * i + 2
    decreases |s| - i
  {
    pairArr := pairArr[i := (s[i], i)];
    i := i + 1;
    steps := steps + 3;
  }
  var pairs := pairArr;
  steps := steps + 1;
  SortCostBound(|s|);
  var sorted := Sort(pairs, (x: (char, int), y: (char, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  SortLength(pairs, (x: (char, int), y: (char, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  steps := steps + SortCost(|s|);
  var removed := seq(|s|, _ => false);
  var z := 0;
  steps := steps + 1;
  while z < |s|
    invariant 0 <= z <= |s|
    invariant |removed| == |s|
    invariant steps <= 2 * z + SortCost(|s|) + 3 * |s| + 4
    decreases |s| - z
  {
    removed := removed[z := false];
    z := z + 1;
    steps := steps + 2;
  }
  var j := 0;
  steps := steps + 1;
  while j < k && j < |sorted|
    invariant 0 <= j <= |sorted|
    invariant |removed| == |s|
    invariant steps <= 3 * j + SortCost(|s|) + 2 * |s| + 3 * |s| + 5
    decreases |sorted| - j
  {
    var target := sorted[j].1;
    if 0 <= target < |s| {
      removed := removed[target := true];
    }
    j := j + 1;
    steps := steps + 3;
  }
  var buf := seq(|s|, _ => ' ');
  var w := 0;
  var m := 0;
  steps := steps + 1;
  while m < |s|
    invariant 0 <= m <= |s|
    invariant 0 <= w <= m
    invariant |buf| == |s| && |removed| == |s|
    invariant steps <= 3 * m + SortCost(|s|) + 5 * |s| + 3 * |s| + 6
    decreases |s| - m
  {
    if !removed[m] {
      buf := buf[w := s[m]];
      w := w + 1;
    }
    m := m + 1;
    steps := steps + 3;
  }
  output := buf[0..w];
  steps := steps + 1;
}
