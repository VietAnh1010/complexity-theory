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

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
  requires n <= |pairs|
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
  // k is an alphabet size: at least 1 (it is a divisor) and at most 26
  requires forall k :: 0 <= k < |pairs| ==> 1 <= pairs[k][1] <= 26
  requires forall k :: 0 <= k < |pairs| ==> pairs[k][0] >= 0
{
  var parts: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t
    decreases n - t
  {
    var nn := pairs[t][0];
    var kk := pairs[t][1];
    var block: string := "";
    var i := 0;
    while i < kk
      invariant 0 <= i
      decreases kk - i
    {
      block := block + [((('a' as int) + i) as char)];
      i := i + 1;
    }
    var reps := nn / kk;
    var rem := nn % kk;
    var s := Repeat(block, reps) + Repeat("a", rem);
    parts := parts + [s];
    t := t + 1;
  }
  output := Join(parts, "\n");
}
