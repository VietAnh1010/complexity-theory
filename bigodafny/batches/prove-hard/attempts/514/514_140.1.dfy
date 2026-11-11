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

include "../../../../prelude.dfy"

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

method Solve(n: int, total_score: int, scores: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |scores| == n
  ensures steps <= 18 * NLogN(n) + 37 * n + 6 + |output|
{
  steps := 0;
  ghost var C := CeilLog2(n);
  ghost var K1 := 8 * (C + 1) + 5;
  ghost var K2 := 8 * (C + 1) + 32;
  var l := total_score;
  var p := scores;
  var idx := 0;
  var ratios: seq<(real, int)> := [];
  while idx < n
    invariant 0 <= idx <= n
    invariant forall x :: x in ratios ==> 1 <= x.1 <= n
    invariant |ratios| == idx
    invariant steps <= idx * K1
    decreases n - idx
  {
    PBound(idx);
    CeilLog2Monotone(idx + 1, n);
    CostMulDistrib(idx, 1, idx + 1, K1);
    steps := steps + 2;
    steps := steps + (4 + Pow2_140_steps(idx));
    var r := p[idx] as real / Pow2_140(idx) as real;
    steps := steps + (3 + |[(r, idx + 1)]|);
    ratios := ratios + [(r, idx + 1)];
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + 1;
  var lessFn := (x: (real, int), y: (real, int)) => x.0 < y.0;
  steps := steps + SortCost(|ratios|);
  var d := Sort(ratios, lessFn);
  SortElemsRI(ratios, lessFn);
  assert forall x :: x in d ==> 1 <= x.1 <= n;
  assert |d| == n;
  SortCostWithin(n, n);
  NK(n, 8, 5);
  NK(n, 8, 32);
  ghost var base := steps;
  assert base <= n * K1 + 1 + 2 * NLogN(n) + 1;
  var res := 1000000000000000000;
  var q := l;
  var curres := 0;
  var k := 0;
  var doneFlag := false;
  while k < |d| && !doneFlag
    invariant forall x :: x in d ==> 1 <= x.1 <= n
    invariant k <= |d|
    invariant steps <= base + k * K2
    decreases |d| - k
  {
    steps := steps + (4 + if k < |d| then 1 else 0);
    steps := steps + 2;
    var idxPos := d[k].1;
    assert d[k] in d;
    PBound(idxPos - 1);
    CeilLog2Monotone(idxPos, n);
    CostMulDistrib(k, 1, k + 1, K2);
    steps := steps + 1;
    if idxPos == 1 {
      steps := steps + 4;
      curres := curres + p[idxPos - 1] * q;
      steps := steps + 2;
      res := if curres < res then curres else res;
      doneFlag := true;
    } else {
      steps := steps + (1 + Pow2_140_steps(idxPos - 1));
      var pw := Pow2_140(idxPos - 1);
      steps := steps + 1;
      var curb := q / pw;
      steps := steps + 4;
      curres := curres + curb * p[idxPos - 1];
      steps := steps + 3;
      var cand := curres + p[idxPos - 1];
      steps := steps + 2;
      res := if cand < res then cand else res;
      steps := steps + 1;
      q := q % pw;
    }
    steps := steps + 1;
    k := k + 1;
  }
  CostMulMonoLeft(k, n, K2);
  IntToStringDigits(res);
  steps := steps + (3 + if k < |d| then 1 else 0);
  steps := steps + (Digits(res) + |"\n"|);
  output := IntToString(res) + "\n";
}

function Pow2_140(e: int): int
  requires e >= 0
  ensures Pow2_140(e) >= 1
  decreases e
{
  if e == 0 then
    1
  else
    var h := Pow2_140(e / 2); if e % 2 == 0 then h * h else 2 * h * h
}

ghost function Pow2_140_steps(e: int): nat
  requires e >= 0
  decreases e
{
  2 + if e == 0 then 0 else 4 + Pow2_140_steps(e / 2) + var h := Pow2_140(e / 2); if e % 2 == 0 then 1 else 2
}

lemma PBound(e: int)
  requires e >= 0
  ensures Pow2_140_steps(e) <= 8 * CeilLog2(e + 1) + 2
  decreases e
{
  if e > 0 {
    PBound(e / 2);
    CeilLog2Monotone(e / 2 + 1, (e + 2) / 2);
  }
}

lemma NK(n: nat, a: nat, b: nat)
  ensures n * (a * (CeilLog2(n) + 1) + b) == a * NLogN(n) + b * n
{
  reveal NLogN();
  CostMulAssoc(n, a, CeilLog2(n) + 1);
  assert n * a == a * n;
}

import opened Prelude
