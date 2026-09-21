// 300_A. Array  (problem 1717, solution 1717_175)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// (input())
// a=sorted(map(int,input().split()))
// b=[a.pop(0)]
// c=a[-1]>0 and [a.pop()] or [a.pop(0),a.pop(0)]
// for l in b,c,a:
//     print(len(l),*l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function FormatLenAndElems(l: seq<int>): string
{
  if |l| == 0 then IntToString(0) else IntToString(|l|) + " " + JoinInts(l, " ")
}

// ---- proof-only scaffolding for the O(n log n) sort -----------------
ghost function SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1 else SortCost(k / 2) + SortCost(k - k / 2) + k
}

ghost function CeilLog2(n: nat): nat
  decreases n
{ if n <= 1 then 0 else 1 + CeilLog2((n + 1) / 2) }

lemma CeilLog2Monotone(m: nat, n: nat)
  requires m <= n
  ensures CeilLog2(m) <= CeilLog2(n)
  decreases n
{
  if n <= 1 { } else if m <= 1 { } else { CeilLog2Monotone((m + 1) / 2, (n + 1) / 2); }
}

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
  requires |a_list| >= 3
  ensures steps <= 2 * |a_list| * (CeilLog2(|a_list|) + 1) + 4 * |a_list| + 20
{
  SortCostNLogN(|a_list|);
  steps := 1 + SortCost(|a_list|);
  var sorted := SortInts(a_list);
  var b := [sorted[0]];
  var rest := sorted[1..];
  var c: seq<int>;
  var a: seq<int>;
  steps := steps + 2;
  if rest[|rest| - 1] > 0 {
    c := [rest[|rest| - 1]];
    a := rest[..|rest| - 1];
  } else {
    c := [rest[0], rest[1]];
    a := rest[2..];
  }
  steps := steps + 3;
  output := FormatLenAndElems(b) + "\n" + FormatLenAndElems(c) + "\n" + FormatLenAndElems(a);
  steps := steps + |b| + |c| + |a| + 6;
}
