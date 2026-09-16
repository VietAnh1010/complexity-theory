// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-16
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both while loops build ga/gb and counts via ga := ga[a_list[i] := i]
//     and counts := counts[o := counts[o]+1], seq functional updates
//     inside n-iteration loops, each costing O(n) and giving O(n**2) total
//     for the Dafny, while the label's m dimension does not exist in the
//     signature and the Python's dict writes ga[a[i]]=i, g[o]=... are O(1)
//     amortized, giving O(n) for the Python.
//
//   how this label could be wrong, and what to check:
//     The label names a dimension m that the signature does not expose
//     (a_list and b_list are both length n, and n is the only size
//     parameter) -- confirm there is no second array or width in Solve's
//     signature, which alone makes O(n*m) wrong. Separately, check whether
//     ga, gb and counts are built via seq functional updates like `ga :=
//     ga[a_list[i] := i]` inside loops of n iterations; if so each update
//     is O(n), making the Dafny O(n**2) even though the Python's dict
//     writes ga[a[i]]=i are O(1).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 39, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "MaxSeq"],
//     "loop_depth": 1, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1365_C. Rotation Matching  (problem 2188, solution 2188_371)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// b=list(map(int,input().split()))
// ga={}
// gb={}
// for i in range(n):ga[a[i]]=i;gb[b[i]]=i
// g={}
// for i in range(1,n+1):o=(gb[i]-ga[i])%n;g[o]=g[o]+1if g.get(o)else 1
// print(max(g[i]for i in g))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
  requires n >= 1
  requires |a_list| == n
  requires |b_list| == n
  requires forall k :: 0 <= k < n ==> 1 <= a_list[k] <= n
  requires forall k :: 0 <= k < n ==> 1 <= b_list[k] <= n
{
  var ga := seq(n + 1, _ => 0);
  var gb := seq(n + 1, _ => 0);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |ga| == n + 1
    invariant |gb| == n + 1
    decreases n - i
  {
    ga := ga[a_list[i] := i];
    gb := gb[b_list[i] := i];
    i := i + 1;
  }
  var counts := seq(if n >= 0 then n else 0, _ => 0);
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant |counts| == n
    decreases n - i + 1
  {
    var o := FloorMod(gb[i] - ga[i], n);
    assert 0 <= o < n by {
      reveal FloorMod();
      reveal FloorDiv();
    }
    counts := counts[o := counts[o] + 1];
    i := i + 1;
  }
  output := IntToString(MaxSeq(counts));
}
