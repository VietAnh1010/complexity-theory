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

include "../../../../prelude.dfy"

lemma Sq2650(n: nat, K: nat)
  requires K == 17 * n + 6
  ensures n * K == 17 * (n * n) + 6 * n
{
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 17 * (n * n) + 18 * n + 4 + |output|
{
  steps := 0;
  var d: map<int, int> := map[];
  var count1 := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= 12 * i
    decreases n - i
  {
    steps := steps + 2;
    steps := steps + 1;
    var e := a_list[i];
    steps := steps + (2 + if e in d then 1 else 0);
    var cur := if e in d then d[e] else 0;
    steps := steps + 2;
    d := d[e := cur + 1];
    steps := steps + 2;
    if cur + 1 == 2 {
      steps := steps + 1;
      count1 := count1 + 1;
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  var result := n;
  steps := steps + 2;
  if |d| == n {
    result := 0;
  }
  ghost var K: nat := 17 * n + 6;
  ghost var B := steps;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= B + i * K
    decreases n - i
  {
    steps := steps + 2;
    var f := d;
    var count2 := count1;
    var j := i;
    var brk := false;
    ghost var s0 := steps;
    while j < n && !brk
      invariant i <= j <= n
      invariant steps <= s0 + 17 * (j - i)
      decreases n - j
    {
      steps := steps + (3 + if j < n then 1 else 0);
      steps := steps + 1;
      var e := a_list[j];
      steps := steps + (3 + if e in f then 1 else 0);
      var cur := (if e in f then f[e] else 0) - 1;
      steps := steps + 1;
      f := f[e := cur];
      steps := steps + 1;
      if cur == 1 {
        steps := steps + 1;
        count2 := count2 - 1;
      }
      steps := steps + 1;
      if count2 == 0 {
        steps := steps + 2;
        var cand := j - i + 1;
        steps := steps + 1;
        if cand < result {
          result := cand;
        }
        brk := true;
      }
      steps := steps + 1;
      j := j + 1;
    }
    steps := steps + (2 + if j < n then 1 else 0);
    steps := steps + 1;
    CostMulDistrib(i, 1, i + 1, K);
    i := i + 1;
  }
  Sq2650(n, K);
  steps := steps + 1;
  steps := steps + Digits(result);
  IntToStringDigits(result);
  output := IntToString(result);
}

import opened Prelude
