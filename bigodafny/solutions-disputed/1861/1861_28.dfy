// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny's outer loop extends every pattern in `pats` and adds a
//     second branch for those ending in i - 1, so `|pats|` grows like
//     Fibonacci in W, and the counting loop walks W entries of each, O(W *
//     phi**W + H * W); the Python's list comprehensions are identical.
//
//   how this label could be wrong, and what to check:
//     The label is polynomial, but `pats` enumerates every valid row of
//     horizontal bars, a Fibonacci number of patterns in W, so building it
//     and the per-column counts costs O(W * phi**W). Check `|pats|` after
//     each round of the outer `while i < W` loop: it follows F(i+1). The
//     statement caps W at 8, which by the value rule does not make it
//     constant.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 98, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 3,
//     "loops": 8, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": true,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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
  requires 1 <= b
  requires 1 <= c <= b
{
  var H := a; var W := b; var K := c;
  var MOD := 1000000007;
  var pats: seq<seq<int>> := [[0]];
  var i := 1;
  while i < W
    invariant 1 <= i <= W
    invariant forall t :: 0 <= t < |pats| ==> |pats[t]| == i
    invariant forall t :: 0 <= t < |pats| ==> forall u :: 0 <= u < |pats[t]| ==> 0 <= pats[t][u] < i
    decreases W - i
  {
    var branch1: seq<seq<int>> := [];
    var j := 0;
    while j < |pats|
      invariant 0 <= j <= |pats|
      invariant forall t :: 0 <= t < |branch1| ==> |branch1[t]| == i + 1
      invariant forall t :: 0 <= t < |branch1| ==> forall u :: 0 <= u < |branch1[t]| ==> 0 <= branch1[t][u] < i + 1
      decreases |pats| - j
    {
      branch1 := branch1 + [pats[j] + [i]];
      j := j + 1;
    }
    var branch2: seq<seq<int>> := [];
    j := 0;
    while j < |pats|
      invariant 0 <= j <= |pats|
      invariant forall t :: 0 <= t < |branch2| ==> |branch2[t]| == i + 1
      invariant forall t :: 0 <= t < |branch2| ==> forall u :: 0 <= u < |branch2[t]| ==> 0 <= branch2[t][u] < i + 1
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
  // iws = [Counter(r) for r in zip(*pats)]
  var iws: seq<map<int, int>> := seq(W, _ => map[]);
  var t := 0;
  while t < |pats|
    invariant 0 <= t <= |pats|
    invariant |iws| == W
    invariant forall q :: 0 <= q < W ==> forall k :: k in iws[q] ==> 0 <= k < W
    decreases |pats| - t
  {
    var u := 0;
    while u < W
      invariant 0 <= u <= W
      invariant |iws| == W
      invariant forall q :: 0 <= q < W ==> forall k :: k in iws[q] ==> 0 <= k < W
      decreases W - u
    {
      var v := pats[t][u];
      var cnt := if v in iws[u] then iws[u][v] else 0;
      iws := iws[u := iws[u][v := cnt + 1]];
      u := u + 1;
    }
    t := t + 1;
  }
  var rs: seq<int> := seq(W, k requires 0 <= k < W => if k == 0 then 1 else 0);
  var row := 0;
  while row < H
    invariant |rs| == W
    decreases H - row
  {
    var newrs: seq<int> := [];
    var col := 0;
    while col < W
      invariant 0 <= col <= W
      invariant |newrs| == col
      decreases W - col
    {
      var iw := iws[col];
      var s := 0;
      var keys := iw.Keys;
      while keys != {}
        invariant keys <= iw.Keys
        decreases |keys|
      {
        var k :| k in keys;
        s := s + rs[k] * iw[k];
        keys := keys - {k};
      }
      newrs := newrs + [s % MOD];
      col := col + 1;
    }
    rs := newrs;
    row := row + 1;
  }
  output := IntToString(rs[K - 1]);
}
