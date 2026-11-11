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

include "../../../../prelude.dfy"

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 64 + 52 * |s| + 8 * NLogN(|s|) + 2 * |output|
{
  steps := 0;
  steps := steps + 1;
  var n := |s|;
  var r := 0;
  var b := 0;
  var y := 0;
  var g := 0;
  var i := 0;
  ghost var K: nat := 15 + 13 * n + 2 * NLogN(n);
  while i < 4 && i < n
    invariant 0 <= i <= 4
    invariant steps <= 1 + i * K
    decreases 4 - i
  {
    ghost var s0 := steps;
    steps := steps + (3 + if i < 4 then 1 else 0);
    var ltrs: seq<char> := [];
    var j := i;
    ghost var s1 := steps;
    assert s1 == s0 + 4;
    while j < n
      invariant steps <= s1 + 6 * |ltrs|
      invariant j > i || j < n
      invariant j < n + 4
      invariant j >= i
      invariant (j - i) % 4 == 0
      invariant |ltrs| == (j - i) / 4
      decreases n - j
    {
      steps := steps + 2;
      steps := steps + (2 + |[s[j]]|);
      ltrs := ltrs + [s[j]];
      steps := steps + 1;
      j := j + 4;
    }
    steps := steps + 1;
    assert |ltrs| >= 1;
    steps := steps + SortCost(|ltrs|);
    var sorted := Sort(ltrs, (x: char, z: char) => x < z);
    SortCostWithin(|ltrs|, n);
    steps := steps + 3;
    var letc := sorted[|sorted| - 1];
    var a := 0;
    var k := 0;
    ghost var s2 := steps;
    while k < |sorted|
      invariant k <= |sorted|
      invariant steps <= s2 + 7 * k
      decreases |sorted| - k
    {
      steps := steps + 3;
      steps := steps + 2;
      if sorted[k] == '!' {
        steps := steps + 1;
        a := a + 1;
      }
      steps := steps + 1;
      k := k + 1;
    }
    steps := steps + 2;
    steps := steps + 1;
    if letc == 'R' {
      steps := steps + 1;
      r := r + a;
    } else if letc == 'B' {
      steps := steps + 1;
      b := b + a;
    } else if letc == 'Y' {
      steps := steps + 1;
      y := y + a;
    } else if letc == 'G' {
      steps := steps + 1;
      g := g + a;
    }
    steps := steps + 1;
    CostMulDistrib(i, 1, i + 1, K);
    i := i + 1;
  }
  CostMulMonoLeft(i, 4, K);
  steps := steps + (2 + if i < 4 then 1 else 0);
  steps := steps + (Digits(r) + |" "| + Digits(b) + |IntToString(b)| + |" "| + Digits(y) + |IntToString(y)| + |" "| + Digits(g) + |IntToString(g)|);
  IntToStringDigits(r);
  IntToStringDigits(b);
  IntToStringDigits(y);
  IntToStringDigits(g);
  output := IntToString(r) + " " + IntToString(b) + " " + IntToString(y) + " " + IntToString(g);
}

import opened Prelude
