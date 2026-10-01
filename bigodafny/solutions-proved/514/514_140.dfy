// 913_C. Party Lemonade  (problem 514, solution 514_140)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, l = map(int, input().split())
// p = list(map(int, input().split()))
// d = []
// d = [[p[i] / 2**i, i + 1] for i in range(n)]
// d.sort(key = lambda x: x[0])
// res = 10**18
// q = l
// curres = 0
// for i in d:
// 	if i[1] == 1:
// 		curres += p[i[1] - 1] * q
// 		res = min(res, curres)
// 		break
// 	curb = q // 2**(i[1] - 1)
// 	curres += curb * p[i[1] - 1]
// 	res = min(res, curres + p[i[1] - 1])
// 	q %= 2**(i[1] - 1)
// print(res)
// --------------------------------------------------------------------

// PROOF NOTE (relation: looser-structural).
// The label is O(nlogn); the proved bound is O(n**2), and the n**2 is the
// translation's Pow2_140, not the algorithm. The Python computes 2**i, one
// integer operation. Dafny has no `**`, so the row computes it with a helper
// recursing i times, and by the decision of 2026-09-23 a helper is charged its
// recursion depth. Called once per element in the first loop (exponents
// 0..n-1) and once per step of the second (exponents up to n-1), it costs
// O(n**2) in total. The sort is O(n log n), bounded by the prelude's
// SortCostNLogN; the rest is linear.

include "../../prelude.dfy"
import opened Prelude

lemma MergeElemsRI(a: seq<(real, int)>, b: seq<(real, int)>, less: ((real, int), (real, int)) -> bool)
  ensures forall x :: x in Merge(a, b, less) ==> x in a || x in b
  decreases |a| + |b|
{
  if |a| == 0 {
  } else if |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeElemsRI(a, b[1..], less);
  } else {
    MergeElemsRI(a[1..], b, less);
  }
}

lemma SortElemsRI(s: seq<(real, int)>, less: ((real, int), (real, int)) -> bool)
  ensures forall x :: x in Sort(s, less) ==> x in s
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortElemsRI(s[..|s| / 2], less);
    SortElemsRI(s[|s| / 2..], less);
    MergeElemsRI(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

// Pow2_140's recursion depth: one level per halving of e.
ghost function Pow2Depth(e: nat): nat
  decreases e
{
  if e == 0 then 1 else 1 + Pow2Depth(e / 2)
}

lemma Pow2DepthBound(e: nat)
  ensures Pow2Depth(e) <= CeilLog2(e + 1) + 1
  decreases e
{
  if e > 0 {
    Pow2DepthBound(e / 2);
    assert (e + 2) / 2 == e / 2 + 1;
  }
}

// a call with 0 <= e < n costs at most CeilLog2(n) + 1
lemma Pow2DepthWithin(e: nat, n: nat)
  requires e < n
  ensures Pow2Depth(e) <= CeilLog2(n) + 1
{
  Pow2DepthBound(e);
  CeilLog2Monotone(e + 1, n);
}

// n * K1 + n * K2 == 2 * NLogN(n) + 12 * n, isolated so Solve's
// verification condition never has to discover it
lemma TwoLoops514(n: nat, K1: nat, K2: nat)
  requires K1 == CeilLog2(n) + 5 && K2 == CeilLog2(n) + 9
  ensures n * K1 + n * K2 == 2 * NLogN(n) + 12 * n
{
  reveal NLogN();
  assert n * K1 == n * (CeilLog2(n) + 1) + 4 * n;
  assert n * K2 == n * (CeilLog2(n) + 1) + 8 * n;
}

method {:vcs_split_on_every_assert} Solve(n: int, total_score: int, scores: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |scores| == n
  ensures steps <= 4 * NLogN(n) + 12 * n + 4
{
  var l := total_score;
  var p := scores;
  var idx := 0;
  var ratios: seq<(real, int)> := [];
  steps := 1;
  ghost var K1: nat := CeilLog2(n) + 5;
  while idx < n
    invariant 0 <= idx <= n
    invariant |ratios| == idx
    invariant forall x :: x in ratios ==> 1 <= x.1 <= n
    invariant steps <= 1 + idx * K1
    decreases n - idx
  {
    // Pow2_140(idx) is charged its recursion depth
    Pow2DepthWithin(idx, n);
    steps := steps + Pow2Depth(idx) + 4;
    var r := (p[idx] as real) / (Pow2_140(idx) as real);
    ratios := ratios + [(r, idx + 1)];
    CostMulDistrib(idx, 1, idx + 1, K1);
    idx := idx + 1;
  }
  var lessFn := (x: (real, int), y: (real, int)) => x.0 < y.0;
  steps := steps + SortCost(n);
  SortCostNLogN(n);
  var d := Sort(ratios, lessFn);
  assert |d| == n;
  assert steps <= 1 + n * K1 + SortCost(n);
  ghost var base := steps;
  ghost var K2: nat := CeilLog2(n) + 9;
  SortElemsRI(ratios, lessFn);
  assert forall x :: x in d ==> 1 <= x.1 <= n;
  var res := 1000000000000000000;
  var q := l;
  var curres := 0;
  var k := 0;
  var doneFlag := false;
  while k < |d| && !doneFlag
    invariant 0 <= k <= |d|
    invariant forall x :: x in d ==> 1 <= x.1 <= n
    invariant steps <= base + k * K2
    decreases |d| - k
  {
    var idxPos := d[k].1;
    assert d[k] in d;
    assert 1 <= idxPos <= n;
    ghost var s0 := steps;
    if idxPos == 1 {
      curres := curres + p[idxPos - 1] * q;
      res := if curres < res then curres else res;
      doneFlag := true;
    } else {
      // Pow2_140(idxPos - 1) is charged its recursion depth
      Pow2DepthWithin(idxPos - 1, n);
      steps := steps + Pow2Depth(idxPos - 1);
      var pw := Pow2_140(idxPos - 1);
      var curb := q / pw;
      curres := curres + curb * p[idxPos - 1];
      var cand := curres + p[idxPos - 1];
      res := if cand < res then cand else res;
      q := q % pw;
    }
    steps := steps + 8;
    assert steps <= s0 + K2;
    CostMulDistrib(k, 1, k + 1, K2);
    k := k + 1;
  }
  // the second loop may stop early, at k < n
  CostMulMonoLeft(k, n, K2);
  assert steps <= base + n * K2;
  assert base <= 1 + n * K1 + 2 * NLogN(n) + 1;
  TwoLoops514(n, K1, K2);
  assert steps <= 2 + 4 * NLogN(n) + 12 * n;
  output := IntToString(res) + "\n";
  steps := steps + 2;
}

// 2**e by squaring: depth log e, as Python's ** is one operation
function Pow2_140(e: int): int
  requires e >= 0
  ensures Pow2_140(e) >= 1
  decreases e
{
  if e == 0 then 1
  else
    var h := Pow2_140(e / 2);
    if e % 2 == 0 then h * h else 2 * h * h
}
