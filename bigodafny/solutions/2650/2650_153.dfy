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

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  requires n >= 1
{
  var d: map<int, int> := map[];
  var count1 := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var e := a_list[i];
    var cur := if e in d then d[e] else 0;
    d := d[e := cur + 1];
    if cur + 1 == 2 { count1 := count1 + 1; }
    i := i + 1;
  }
  var result := n;
  if |d| == n { result := 0; }
  i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var f := d;
    var count2 := count1;
    var j := i;
    var brk := false;
    while j < n && !brk
      invariant i <= j <= n
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
    }
    i := i + 1;
  }
  output := IntToString(result);
}
