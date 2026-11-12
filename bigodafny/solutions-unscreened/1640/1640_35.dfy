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

lemma MaxSeqFromBound(s: seq<int>, i: nat, best: int)
  requires i <= |s|
  ensures MaxSeqFrom(s, i, best) >= best
  ensures forall k :: i <= k < |s| ==> s[k] <= MaxSeqFrom(s, i, best)
  decreases |s| - i
{
  if i < |s| {
    MaxSeqFromBound(s, i + 1, if s[i] > best then s[i] else best);
  }
}

lemma GcdPos(a: int, b: int)
  requires a >= 0 && b >= 0
  requires a > 0 || b > 0
  ensures Gcd(a, b) > 0
  decreases b
{
  if b > 0 {
    GcdPos(b, a % b);
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires exists j, k :: 0 <= j < |a_list| && 0 <= k < |a_list| && a_list[j] != a_list[k]
{
  var m := MaxSeq(a_list);
  MaxSeqFromBound(a_list, 1, a_list[0]);
  assert forall k :: 0 <= k < |a_list| ==> a_list[k] <= m;
  var g := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant g >= 0
    invariant g == 0 ==> forall k :: 0 <= k < i ==> a_list[k] == m
    decreases |a_list| - i
  {
    if g > 0 || m - a_list[i] > 0 {
      GcdPos(g, m - a_list[i]);
    }
    g := Gcd(g, m - a_list[i]);
    i := i + 1;
  }
  assert g > 0;
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
