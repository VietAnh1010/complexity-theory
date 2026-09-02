// p03222 AtCoder Beginner Contest 113 - Number of Amidakuji  (problem 1861, solution 1861_28)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// 
// H, W, K = [int(_) for _ in input().split()]
// 
// MOD = 1000000007
// 
// pats = [[0]]
// 
// for i in range(1, W):
//     pats = [p + [i] for p in pats] + [p[:-1] + [i, i - 1] for p in pats if p[-1] == i - 1]
// 
// iws = [Counter(r) for r in zip(*pats)]
// 
// rs = [1] + [0] * (W - 1)
// 
// for j in range(H):
//     rs = [sum(rs[i] * iw[i] for i in iw) % MOD for iw in iws]
// 
// print(rs[K - 1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
{
  var H := a; var W := b; var K := c;
  var MOD := 1000000007;
  var pats: seq<seq<int>> := [[0]];
  var i := 1;
  while i < W
    decreases W - i
  {
    var branch1: seq<seq<int>> := [];
    var j := 0;
    while j < |pats|
      decreases |pats| - j
    {
      branch1 := branch1 + [pats[j] + [i]];
      j := j + 1;
    }
    var branch2: seq<seq<int>> := [];
    j := 0;
    while j < |pats|
      decreases |pats| - j
    {
      var p := pats[j];
      if p[|p| - 1] == i - 1 {
        branch2 := branch2 + [p[..|p| - 1] + [i, i - 1]];
      }
      j := j + 1;
    }
    pats := branch1 + branch2;
    i := i + 1;
  }
  var rs: seq<int> := seq(W, k requires 0 <= k < W => if k == 0 then 1 else 0);
  var row := 0;
  while row < H
    decreases H - row
  {
    var newrs: seq<int> := [];
    var col := 0;
    while col < W
      decreases W - col
    {
      var s := 0;
      var pi := 0;
      while pi < |pats|
        decreases |pats| - pi
      {
        s := (s + rs[pats[pi][col]]) % MOD;
        pi := pi + 1;
      }
      newrs := newrs + [s];
      col := col + 1;
    }
    rs := newrs;
    row := row + 1;
  }
  output := IntToString(rs[K - 1]);
}
