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
// bound on it. This copy proves the true O(k log k) via a recursion-tree
// argument over a ceiling log; solutions-verified/ keeps the weaker quadratic
// bound. Both are assumption-free.

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

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires |numbers| == n
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 2 * n + 4
{
  SortCostNLogN(n);
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
  assert SortCost(n) <= 2 * n * (CeilLog2(n) + 1) + 1;
  steps := steps + 1;
}
