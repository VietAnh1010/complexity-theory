// 186_A. Comparing Strings  (problem 1243, solution 1243_0)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// g1=list(input())
// g2=list(input())
// cntr=0
// if sorted(g1)!=sorted(g2):
//     print('NO')
// else:
//     for i in range(len(g1)):
//         if g1[i]!=g2[i]:
//                 cntr=cntr+1
//     if cntr==2:
//         print('YES')
//     else:
//         print('NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
//
// Two sorts, one per input line, so the bound carries two independent
// recursion-tree terms and the label's `nlogn+mlogm` shape is visible in the
// postcondition rather than collapsed into one parameter.
//
// Prelude.Sort is a plain recursive merge sort and lives in prelude.dfy, which
// a proof may not instrument, so its cost is charged through SortCost, whose
// recursion mirrors Sort's own split. SortCostNLogN proves the tight bound by
// a recursion-tree argument over a CEILING log: both halves of a split of size
// k are at most ceil(k/2), and CeilLog2(ceil(k/2)) == CeilLog2(k) - 1 holds by
// definition. With a floor log the inductive step is false at k = 3.
//
// The sequence comparison `a != b` is charged |s1| + |s2|, elementwise, the
// same charge the table gives `multiset(a) == multiset(b)`.

ghost function SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1
  else SortCost(k / 2) + SortCost(k - k / 2) + k
}

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

// The equality test sorts, as the Python does. An earlier translation compared
// multisets instead: same answer on every test, one complexity class cheaper,
// and the O(nlogn+mlogm) label then described nothing in this file.
method Solve(s1: string, s2: string) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |s1| * (CeilLog2(|s1|) + 1)
                 + 2 * |s2| * (CeilLog2(|s2|) + 1)
                 + 3 * |s1| + |s2| + 5
{
  SortCostNLogN(|s1|);
  SortCostNLogN(|s2|);

  var a := Sort(s1, (x: char, y: char) => x < y);
  var b := Sort(s2, (x: char, y: char) => x < y);
  steps := 1 + SortCost(|s1|) + SortCost(|s2|);

  // one elementwise comparison of the two sorted lines
  steps := steps + |s1| + |s2| + 1;

  if a != b {
    output := "NO";
  } else {
    assert |s1| == |a| == |b| == |s2|;
    ghost var base := steps;
    var cntr := 0;
    var i := 0;
    while i < |s1|
      invariant 0 <= i <= |s1|
      invariant steps == base + 2 * i
      decreases |s1| - i
    {
      if s1[i] != s2[i] { cntr := cntr + 1; }
      i := i + 1;
      steps := steps + 2;
    }
    output := if cntr == 2 then "YES" else "NO";
  }
  steps := steps + 1;
}
