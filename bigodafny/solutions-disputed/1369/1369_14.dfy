// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n+mlogm)
//   cause          : label
//   confidence     : low
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny's two greedy sweeps cost O(N) and `SortInts(right)` sorts
//     K values, so the total is O(N + K log K) with K read from input; the
//     Python's `right.sort()` sorts the same K values.
//
//   how this label could be wrong, and what to check:
//     The sort is over `right`, which holds exactly K entries, not N; the
//     sweeps are O(N). So the cost is O(N + K log K) with K a separate
//     input. Check that `right` has length K; if a reviewer treats K <= N
//     as the same size, the label stands.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 67, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 3, "recursive_helpers": 2,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["SortInts"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// p02721 AtCoder Beginner Contest 161 - Yutori  (problem 1369, solution 1369_14)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N, K, C = map(int, input().split())
// S = input()
// left = []
// right = []
// i, j = 0, N-1
// while len(left) <= K-1:
//     if S[i] == "o":
//         left.append(i)
//         i += C+1
//     else:
//         i += 1
// while len(right) <= K-1:
//     if S[j] == "o":
//         right.append(j)
//         j -= C+1
//     else:
//         j -= 1
// right.sort()
// for n in range(K):
//     if left[n] == right[n]:
//         print(left[n] + 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function GreedyL(s: string, C: int, pos: int): nat
  requires C >= 0 && pos >= 0
  decreases |s| - pos
{
  if pos >= |s| then 0
  else if s[pos] == 'o' then 1 + GreedyL(s, C, pos + C + 1)
  else GreedyL(s, C, pos + 1)
}

function GreedyR(s: string, C: int, pos: int): nat
  requires C >= 0 && pos < |s|
  decreases pos + 1
{
  if pos < 0 then 0
  else if s[pos] == 'o' then 1 + GreedyR(s, C, pos - C - 1)
  else GreedyR(s, C, pos - 1)
}

method Solve(n: int, a: int, b: int, s: string) returns (output: string)
  requires n == |s| && a >= 1 && b >= 0
  requires GreedyL(s, b, 0) >= a
  requires GreedyR(s, b, n - 1) >= a
{
  var N := n;
  var K := a;
  var C := b;
  var left: seq<int> := [];
  var right: seq<int> := [];
  var i := 0;
  while |left| <= K - 1
    invariant |left| <= K && i >= 0
    invariant |left| + GreedyL(s, C, i) >= K
    decreases K - |left|, |s| - i
  {
    if s[i] == 'o' {
      left := left + [i];
      i := i + C + 1;
    } else {
      i := i + 1;
    }
  }
  var j := N - 1;
  while |right| <= K - 1
    invariant |right| <= K && j < |s|
    invariant |right| + GreedyR(s, C, j) >= K
    decreases K - |right|, j + 1
  {
    if s[j] == 'o' {
      right := right + [j];
      j := j - C - 1;
    } else {
      j := j - 1;
    }
  }
  right := SortInts(right);
  var parts: seq<string> := [];
  var k := 0;
  while k < K
    decreases K - k
  {
    if left[k] == right[k] {
      parts := parts + [IntToString(left[k] + 1)];
    }
    k := k + 1;
  }
  output := Join(parts, "\n");
}
