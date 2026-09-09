// 984_A. Game  (problem 187, solution 187_193)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=input().split()
// for i in range(n):
//     a[i]=int(a[i])
// a=sorted(a)
// if n%2==0:
//     print(a[(n//2)-1])
// else:
//     print(a[(n//2)])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(nlogn) -- agrees, and this is the first row to get the TIGHT bound on
// the first pass. 603_284 and 1484_82 each needed a quadratic fallback in this
// directory and a second copy in solutions-nlogn/ carrying the real bound; the
// recursion-tree argument is reusable, so this row skips that step.
//
// Prelude.Sort is a plain recursive merge sort and lives in prelude.dfy, which
// a row may not instrument. Its cost is therefore charged as SortCost, a ghost
// function whose recursion mirrors Sort's own split, and bounded below.
//
// The ceiling log is what makes the induction close: both halves of a split of
// size k are at most ceil(k/2), so CeilLog2(ceil(k/2)) == CeilLog2(k) - 1 holds
// by definition. With a floor log that step is false at k = 3. Note the
// contrast with 945_255 in this directory, which halves by rounding DOWN and so
// wants a FLOOR log -- the log must round the way the code rounds.
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

// Z3 does not do nonlinear arithmetic. Every multiplication the main argument
// needs is isolated here so the solver never has to discover one.
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

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 6
{
  SortCostNLogN(n);
  steps := 1 + SortCost(n);
  var sorted := SortInts(a_list);
  var idx := if n % 2 == 0 then n / 2 - 1 else n / 2;
  output := IntToString(sorted[idx]);
  steps := steps + 4;
}
