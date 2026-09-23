// 1092_A. Uniform String  (problem 2254, solution 2254_143)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for i in range(int(input())):
//     n,k=map(int,input().split())
//     s=""
//     x=0
//     for i in range(0,n):
//         s=s+chr(x+97)
//         x+=1
//         x=x%k
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Sum of the per-test-case string lengths pairs[0..t][0] -- a real ghost
// cost, since each test's inner loop does pairs[k][0] work (a value
// parameter, per the value-vs-size convention).
ghost function SumFirst(pairs: seq<seq<int>>, t: nat): nat
  requires t <= |pairs|
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2 && pairs[k][0] >= 0
  decreases t
{
  if t == 0 then 0 else SumFirst(pairs, t - 1) + pairs[t - 1][0] as nat
}

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n <= |pairs|
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
  // k is an alphabet size: at least 1 (it is a divisor) and at most 26
  requires forall k :: 0 <= k < |pairs| ==> 1 <= pairs[k][1] <= 26
  requires n >= 0
  requires forall k :: 0 <= k < |pairs| ==> pairs[k][0] >= 0
  ensures steps <= 4 * SumFirst(pairs, n) + 3 * n + |output| + 3
{
  var parts: seq<string> := [];
  var t := 0;
  steps := 1;
  ghost var base1 := steps;
  while t < n
    invariant 0 <= t <= n
    invariant |parts| == t
    invariant steps <= base1 + 4 * SumFirst(pairs, t) + 3 * t
    decreases n - t
  {
    var nn := pairs[t][0];
    var kk := pairs[t][1];
    var s: string := "";
    var x := 0;
    var i := 0;
    ghost var base2 := steps;
    while i < nn
      invariant 0 <= x < kk
      invariant 0 <= i <= nn
      invariant steps <= base2 + 4 * i
      decreases nn - i
    {
      s := s + [((x + 97) as char)];
      x := x + 1;
      x := x % kk;
      i := i + 1;
      steps := steps + 4;
    }
    parts := parts + [s];
    t := t + 1;
    steps := steps + 3;
    assert nn == pairs[t - 1][0];
    assert SumFirst(pairs, t) == SumFirst(pairs, t - 1) + nn as nat;
  }
  output := Join(parts, "\n");
  steps := steps + |output| + 2;
}
