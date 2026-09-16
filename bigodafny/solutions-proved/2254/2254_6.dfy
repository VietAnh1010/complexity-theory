// 1092_A. Uniform String  (problem 2254, solution 2254_6)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// """https://codeforces.com/contest/1092/problem/A"""
// alpha = 'abcdefghijklmnopqrstuvwxyz'
// for _ in range(int(input())):
//     n, k = tuple(map(int,input().split()))
//     s = alpha[:k]*(n//k) + 'a'*(n%k)
//     print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// kk is bounded 1..26 by `requires`, so the inner block-building loop is
// O(1) per test case. Repeat(block, reps) and Repeat("a", rem) are charged by
// output length; reps*|block| + rem <= nn, so each test case costs O(nn).
// Bound is stated over the sum of the nn values, the honest measure of the
// total output size the label's "n" refers to.
ghost function SumFirst(pairs: seq<seq<int>>, upto: nat): nat
  requires upto <= |pairs|
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2 && pairs[k][0] >= 0
{
  if upto == 0 then 0 else SumFirst(pairs, upto - 1) + pairs[upto - 1][0]
}

lemma RepeatLength(s: string, n: nat)
  ensures |Repeat(s, n)| == |s| * n
  decreases n
{
  if n == 0 {
  } else {
    RepeatLength(s, n - 1);
  }
}

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n <= |pairs|
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
  // k is an alphabet size: at least 1 (it is a divisor) and at most 26
  requires forall k :: 0 <= k < |pairs| ==> 1 <= pairs[k][1] <= 26
  requires forall k :: 0 <= k < |pairs| ==> pairs[k][0] >= 0
  ensures n >= 0 ==> steps <= 40 * n + 3 * SumFirst(pairs, n) + 4
{
  steps := 1;
  var parts: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t
    invariant n >= 0 ==> t <= n
    invariant t <= |pairs|
    invariant steps <= 40 * t + 3 * SumFirst(pairs, t) + 2
    decreases n - t
  {
    var nn := pairs[t][0];
    var kk := pairs[t][1];
    var block: string := "";
    var i := 0;
    steps := steps + 2;
    while i < kk
      invariant 0 <= i <= kk
      invariant |block| == i
      invariant steps <= 40 * t + 3 * SumFirst(pairs, t) + 4 + i
      decreases kk - i
    {
      block := block + [((('a' as int) + i) as char)];
      i := i + 1;
      steps := steps + 1;
    }
    var reps := nn / kk;
    var rem := nn % kk;
    steps := steps + 2;
    RepeatLength(block, reps);
    RepeatLength("a", rem);
    // |block| == kk (built one char per iteration above), reps == nn / kk,
    // so |Repeat(block, reps)| == kk * (nn / kk) <= nn; |Repeat("a", rem)|
    // == rem == nn % kk <= nn. Charge each Repeat call by its output length.
    assert |block| == kk;
    var s := Repeat(block, reps) + Repeat("a", rem);
    parts := parts + [s];
    t := t + 1;
    steps := steps + 2 * nn + 3;
  }
  output := Join(parts, "\n");
  steps := steps + 2;
}
