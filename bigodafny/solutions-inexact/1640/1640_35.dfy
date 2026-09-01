// 1216_D. Swords  (problem 1640, solution 1640_35)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import gcd
// n = int(input())
// A = list(map(int, input().split()))
// m = max(A)
// g = 0
// for i in A:
//     g = gcd(g, m - i)
// ans = 0
// for i in A:
//     ans += (m - i) // g
// print(ans, g)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var m := MaxSeq(a_list);
  var g := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    g := Gcd(g, m - a_list[i]);
    i := i + 1;
  }
  var ans := 0;
  i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    ans := ans + (m - a_list[i]) / g;
    i := i + 1;
  }
  output := IntToString(ans) + " " + IntToString(g);
}
