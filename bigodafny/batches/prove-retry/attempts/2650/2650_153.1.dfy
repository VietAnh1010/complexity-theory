// 1208_B. Uniqueness  (problem 2650, solution 2650_153)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// lst = [int(i) for i in input().split()]
// d, count1 = {}, 0
// for elem in lst:
//     d[elem] = d.get(elem, 0) + 1
//     if d[elem] == 2:
//         count1 += 1
// result = n
// if len(d) == n:
//     result = 0
// for i in range(n):
//     f = d.copy()
//     count2 = count1
//     for j in range(i, n):
//         f[lst[j]] -= 1
//         if f[lst[j]] == 1:
//             count2 -= 1
//         if count2 == 0:
//             result = min(result, j - i + 1)
//             break
// print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma Sq2650(n: nat, K: nat)
  requires K == 13 * n + 10
  ensures n * K == 13 * (n * n) + 10 * n
{
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 13 * (n * n) + 30 * n + 30 + |output|
{
  steps := 1;
  var d: map<int, int> := map[];
  var count1 := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |d| <= i
    invariant steps == 1 + 8 * i
    decreases n - i
  {
    var e := a_list[i];
    var cur := if e in d then d[e] else 0;
    d := d[e := cur + 1];
    if cur + 1 == 2 { count1 := count1 + 1; }
    i := i + 1;
    steps := steps + 8;
  }
  var result := n;
  if |d| == n { result := 0; }
  steps := steps + 3;
  ghost var K: nat := 13 * n + 10;
  ghost var B := steps;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= B + i * K
    decreases n - i
  {
    var f := d;
    var count2 := count1;
    var j := i;
    var brk := false;
    ghost var s0 := steps + |d| + 3;
    steps := s0;
    while j < n && !brk
      invariant i <= j <= n
      invariant steps <= s0 + 12 * (j - i)
      decreases n - j
    {
      var e := a_list[j];
      var cur := (if e in f then f[e] else 0) - 1;
      f := f[e := cur];
      if cur == 1 { count2 := count2 - 1; }
      if count2 == 0 {
        var cand := j - i + 1;
        if cand < result { result := cand; }
        brk := true;
      }
      j := j + 1;
      steps := steps + 12;
    }
    CostMulDistrib(i, 1, i + 1, K);
    i := i + 1;
  }
  Sq2650(n, K);
  IntToStringDigits(result);
  output := IntToString(result);
  steps := steps + Digits(result);
}
