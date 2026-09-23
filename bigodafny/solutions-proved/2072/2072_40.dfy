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

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma MulDistrib(a: nat, b: nat, k: nat, L: nat)
  requires a + b == k
  ensures a * L + b * L == k * L
{ }

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
