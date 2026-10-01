// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : both
//   confidence     : low
//   auditor        : labelaudit-r3d-05
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Dafny's main loop runs H times, then W columns, then scans every
//     pattern in pats (about Fibonacci(W) of them), giving O(H*W*|pats|)
//     with |pats| exponential in W. The Python builds Counter objects once
//     and then does O(H*W**2) per-row work, so the Python is not O(n**2)
//     and the Dafny is in a worse class than the Python; I lean both, with
//     low confidence on the cause.
//
//   how this label could be wrong, and what to check:
//     The label assumes polynomial growth in a size n, but the input is
//     three values (H, W, K) and the cost is exponential in W. Check the
//     pats construction, whose size grows like Fibonacci in W, and the row
//     loop that scans all of pats for every column; the Python's Counter
//     aggregation (iws) avoids that per-row factor.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 76, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 3,
//     "loops": 6, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
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
  var rs: seq<int> := seq(W, k requires 0 <= k < W => if k == 0 then 1 else 0);
  var row := 0;
  while row < H
    invariant |rs| == W
    invariant forall t :: 0 <= t < |pats| ==> |pats[t]| == W
    invariant forall t :: 0 <= t < |pats| ==> forall u :: 0 <= u < |pats[t]| ==> 0 <= pats[t][u] < W
    decreases H - row
  {
    var newrs: seq<int> := [];
    var col := 0;
    while col < W
      invariant 0 <= col <= W
      invariant |newrs| == col
      decreases W - col
    {
      var s := 0;
      var pi := 0;
      while pi < |pats|
        invariant 0 <= pi <= |pats|
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
