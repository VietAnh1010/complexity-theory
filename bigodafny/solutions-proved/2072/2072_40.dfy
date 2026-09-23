// 758_B. Blown Garland  (problem 2072, solution 2072_40)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// arr = input()
// n = len(arr)
// r, b, y, g = 0, 0, 0, 0
//
// for i in range(4):
//     if i >= n:
//         break
//     ltrs = sorted(arr[i::4])
//     let = ltrs[len(ltrs) - 1]
//     a = ltrs.count('!')
//     if let == 'R':
//         r += a
//     elif let == 'B':
//         b += a
//     elif let == 'Y':
//         y += a
//     elif let == 'G':
//         g += a
//
// print(r, b, y, g)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Sort's own cost via the standard T(k) = T(k/2) + T(k-k/2) + k recurrence,
// bounded O(k log k) -- precedent solutions-proved/1563/1563_497.dfy.
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

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * (SortCost(|s|) + 3 * |s| + 10) + |output| + 10
{
  var n := |s|;
  var r := 0;
  var b := 0;
  var y := 0;
  var g := 0;
  var i := 0;
  steps := 1;
  ghost var base1 := steps;
  ghost var outer := 0;
  ghost var C := SortCost(n) + 3 * n + 10;
  while i < 4 && i < n
    invariant 0 <= i <= 4
    invariant outer == i
    invariant steps <= base1 + outer * C
    decreases 4 - i
  {
    var ltrs: seq<char> := [];
    var j := i;
    ghost var base2 := steps;
    ghost var cnt := 0;
    while j < n
      invariant j >= i
      invariant (j - i) % 4 == 0
      invariant |ltrs| == (j - i) / 4
      invariant |ltrs| <= n
      invariant cnt == |ltrs|
      invariant steps <= base2 + 2 * cnt
      decreases n - j
    {
      ltrs := ltrs + [s[j]];
      j := j + 4;
      cnt := cnt + 1;
      steps := steps + 2;
    }
    assert |ltrs| <= n;
    assert steps <= base2 + 2 * n;
    var sorted := Sort(ltrs, (x: char, z: char) => x < z);
    steps := steps + SortCost(n);
    var letc := sorted[|sorted| - 1];
    var a := 0;
    var k := 0;
    ghost var base3 := steps;
    ghost var cnt2 := 0;
    while k < |sorted|
      invariant 0 <= k <= |sorted|
      invariant |sorted| == |ltrs|
      invariant cnt2 == k
      invariant steps <= base3 + cnt2
      decreases |sorted| - k
    {
      if sorted[k] == '!' {
        a := a + 1;
      }
      k := k + 1;
      cnt2 := cnt2 + 1;
      steps := steps + 1;
    }
    if letc == 'R' {
      r := r + a;
    } else if letc == 'B' {
      b := b + a;
    } else if letc == 'Y' {
      y := y + a;
    } else if letc == 'G' {
      g := g + a;
    }
    assert steps <= base1 + outer * C + (SortCost(n) + 3 * n + 8);
    assert SortCost(n) + 3 * n + 8 <= C;
    MulDistrib(outer, 1, outer + 1, C);
    assert outer * C + C == (outer + 1) * C;
    i := i + 1;
    outer := outer + 1;
    steps := steps + 8;
  }
  MulMonoRight(C, outer, 4);
  assert outer * C <= 4 * C;
  output := IntToString(r) + " " + IntToString(b) + " " + IntToString(y) + " " + IntToString(g);
  steps := steps + |output| + 5;
}
