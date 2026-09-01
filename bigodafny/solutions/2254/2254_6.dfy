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
{
  var parts: seq<string> := [];
  var t := 0;
  while t < n
    decreases n - t
  {
    var nn := pairs[t][0];
    var kk := pairs[t][1];
    var block: string := "";
    var i := 0;
    while i < kk
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
