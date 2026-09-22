// 441_B. Valera and Fruits  (problem 2423, solution 2423_48)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
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
//   This row was unprovable until 2026-09-22. The outer loop runs
//   `d[|d|-1].0 + 2` times -- the largest first component AFTER SORTING --
//   and prelude.dfy proved only SortIsPermutation, that the sorted output
//   holds the same elements as the input. Nothing said it was in ORDER, so
//   the trip count could not be tied to anything about `pairs` and could not
//   even be named. SortIsSorted and SortLastIsMax were added to the prelude
//   for exactly this; LastIsMaxFirst below is the two-line consequence.
//
//   The inner loops are amortised, not nested: `idx` never resets, so their
//   total work across every outer iteration is at most n, which is why the
//   bound carries `2 * n` and not `n * OuterTrips`.
//
//   IntToString(r) is charged 1 here, matching 2586_20. Note that 276_610
//   charges it by digit count. The corpus is inconsistent on this and the
//   difference is not settled; it does not change this row's relation, which
//   is decided by the OuterTrips term.
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def a():	
// 	n, v = list(map(int, input().split(" ")))
// 	d = []
// 	for i in range(n):
// 		d.append(list(map(int, input().split(" "))))
// 	d.sort()
// 
// 	cur = 0
// 	nex = 0
// 	k = 0
// 	r = 0
// 	for i in range(d[-1][0] + 2):
// 		nex = 0
// 		p = v
// 		if k != n:
// 			while(d[k][0] < i):
// 				k += 1
// 				if k == n:
// 					break
// 		if k != n:
// 			while(d[k][0] == i):
// 				nex += d[k][1]
// 				k += 1
// 				if k == n:
// 					break
// 		r += min(p, cur)
// 		p -= min(p, cur)
// 		r += min(p, nex)
// 		cur = nex - min(p, nex)
// 	return r
// 
// print(a())
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

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


// ---- n log n recursion-tree argument -------------------------------------
// Ceiling log. The recursive step is ceil(n/2), not floor(n/2), which is what
// makes the induction close: both halves of a split of size k are at most
// ceil(k/2), and CeilLog2(ceil(k/2)) = CeilLog2(k) - 1 holds by definition.
// With floor-log that step is false at k = 3.
ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

lemma CeilLog2Monotone(m: nat, n: nat)
  requires m <= n
  ensures CeilLog2(m) <= CeilLog2(n)
  decreases n
{
  if n <= 1 { }
  else if m <= 1 { }
  else { CeilLog2Monotone((m + 1) / 2, (n + 1) / 2); }
}

// Z3 does not do nonlinear arithmetic well. Every multiplication step the main
// proof needs is isolated here so the solver never has to discover one.
lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma MulDistrib(a: nat, b: nat, k: nat, L: nat)
  requires a + b == k
  ensures a * L + b * L == k * L
{ }

lemma SortCostNLogN(k: nat)
  ensures SortCost(k) <= 2 * k * (CeilLog2(k) + 1) + 1
  decreases k
{
  if k <= 1 { return; }
  var a := k / 2;
  var b := k - k / 2;
  var L := CeilLog2(k);
  assert a + b == k;
  assert b == (k + 1) / 2;
  assert a <= b;
  SortCostNLogN(a);
  SortCostNLogN(b);
  CeilLog2Monotone(a, b);
  assert L == 1 + CeilLog2(b);
  assert CeilLog2(a) + 1 <= L;
  assert CeilLog2(b) + 1 == L;
  MulMonoRight(2 * a, CeilLog2(a) + 1, L);
  MulMonoRight(2 * b, CeilLog2(b) + 1, L);
  assert SortCost(a) <= 2 * a * L + 1;
  assert SortCost(b) <= 2 * b * L + 1;
  MulDistrib(2 * a, 2 * b, 2 * k, L);
  assert 2 * a * L + 2 * b * L == 2 * k * L;
  assert SortCost(k) == SortCost(a) + SortCost(b) + k;
  assert SortCost(k) <= 2 * k * L + k + 2;
  assert 2 * k * (L + 1) == 2 * k * L + 2 * k;
  assert k + 2 <= 2 * k + 1;
}


ghost function MaxFirst(s: seq<(int, int)>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0].0
  else var m := MaxFirst(s[1..]); if s[0].0 > m then s[0].0 else m
}

lemma MaxFirstBounds(s: seq<(int, int)>)
  requires |s| > 0
  ensures forall x :: x in s ==> x.0 <= MaxFirst(s)
  decreases |s|
{
  if |s| == 1 {
    forall x | x in s ensures x.0 <= MaxFirst(s) { assert x == s[0]; }
  } else {
    MaxFirstBounds(s[1..]);
    forall x | x in s ensures x.0 <= MaxFirst(s) {
      if x != s[0] {
        var i :| 0 <= i < |s| && s[i] == x;
        if i > 0 { assert s[1..][i-1] == x; assert x in s[1..]; }
      }
    }
  }
}

// The point of the exercise: the sorted sequence's last first-component is
// MaxFirst of the INPUT. Before prelude.dfy had SortIsSorted and SortLastIsMax
// this could not be stated at all, because nothing said Sort produced an
// ordered sequence -- only that it was a permutation.
//
// `less` is a parameter rather than a named constant on purpose: a ghost
// function returning a lambda gives Dafny a value it will not identify with
// the same lambda written at the call site, and every fact about Sort then
// fails to transfer.
lemma LastIsMaxFirst(pairs: seq<(int, int)>, less: ((int, int), (int, int)) -> bool)
  requires |pairs| > 0
  requires StrictTotalOrder(less)
  requires forall a: (int, int), b: (int, int) :: !less(a, b) ==> b.0 <= a.0
  ensures |Sort(pairs, less)| == |pairs|
  ensures Sort(pairs, less)[|pairs| - 1].0 == MaxFirst(pairs)
{
  var d := Sort(pairs, less);
  SortLastIsMax(pairs, less);
  SortKeepsElems(pairs, less);
  MaxFirstBounds(pairs);
  MaxFirstAttained(pairs);

  assert d[|d| - 1] in d;
  assert d[|d| - 1] in pairs;              // SortKeepsElems
  assert d[|d| - 1].0 <= MaxFirst(pairs);  // MaxFirstBounds

  var w :| w in pairs && w.0 == MaxFirst(pairs);
  assert !less(d[|d| - 1], w);             // SortLastIsMax
  assert w.0 <= d[|d| - 1].0;              // the refinement hypothesis
}

lemma MaxFirstAttained(s: seq<(int, int)>)
  requires |s| > 0
  ensures exists w :: w in s && w.0 == MaxFirst(s)
  decreases |s|
{
  if |s| == 1 { assert s[0] in s && s[0].0 == MaxFirst(s); }
  else {
    MaxFirstAttained(s[1..]);
    var m := MaxFirst(s[1..]);
    if s[0].0 > m { assert s[0] in s && s[0].0 == MaxFirst(s); }
    else {
      var w :| w in s[1..] && w.0 == m;
      assert w in s;
    }
  }
}

// The outer loop runs `d[|d|-1].0 + 2` times, clamped at zero. That is an
// input VALUE, not a size, so it appears in the bound as its own parameter.
ghost function OuterTrips(pairs: seq<(int, int)>): nat
  requires |pairs| > 0
{
  var m := MaxFirst(pairs) + 2;
  if m > 0 then m else 0
}

method Solve(n: int, k: int, pairs: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires |pairs| >= 1
  requires n <= |pairs|
  requires n >= 0
  ensures steps <= 2 * |pairs| * (CeilLog2(|pairs|) + 1)
                 + 12 * OuterTrips(pairs) + 2 * n + 21
{
  var less := (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1);
  assert StrictTotalOrder(less);
  assert forall a: (int, int), b: (int, int) :: !less(a, b) ==> b.0 <= a.0;

  SortCostNLogN(|pairs|);
  var d := Sort(pairs, less);
  steps := 1 + SortCost(|pairs|);

  LastIsMaxFirst(pairs, less);
  assert |d| == |pairs|;

  var cur := 0;
  var nex := 0;
  var idx := 0;
  var r := 0;
  var limit := d[|d| - 1].0 + 2;
  assert limit == MaxFirst(pairs) + 2;
  assert limit <= OuterTrips(pairs);
  steps := steps + 5;

  ghost var base := steps;
  var i := 0;
  while i < limit
    invariant 0 <= i
    invariant i <= OuterTrips(pairs)   // 0 when limit <= 0, where the loop never runs
    invariant 0 <= idx <= n
    invariant |d| == |pairs|
    invariant limit == MaxFirst(pairs) + 2
    invariant steps <= base + 12 * i + 2 * idx
    decreases limit - i
  {
    nex := 0;
    var p := k;
    while idx < n && d[idx].0 < i
      invariant 0 <= idx <= n
      invariant steps <= base + 12 * i + 2 * idx
      decreases n - idx
    {
      idx := idx + 1;
      steps := steps + 2;
    }
    while idx < n && d[idx].0 == i
      invariant 0 <= idx <= n
      invariant steps <= base + 12 * i + 2 * idx
      decreases n - idx
    {
      nex := nex + d[idx].1;
      idx := idx + 1;
      steps := steps + 2;
    }
    var m1 := if p < cur then p else cur;
    r := r + m1;
    p := p - m1;
    var m2 := if p < nex then p else nex;
    r := r + m2;
    cur := nex - m2;
    i := i + 1;
    steps := steps + 12;
  }
  assert i <= OuterTrips(pairs);
  assert steps <= base + 12 * OuterTrips(pairs) + 2 * n;

  output := IntToString(r);
  steps := steps + 1;
}
