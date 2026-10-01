// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(nlogn)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Segment building appends O(1) per element, and each run longer than
//     k is sorted in O(len log len) and summed by SumSeq, so the total is
//     O(n log n); the Python sorts the same runs, so the O(n**2) label
//     matches neither.
//
//   how this label could be wrong, and what to check:
//     The label O(n**2) assumes quadratic work, but the Dafny's loops are
//     one pass over |s| building segments and one pass over segments,
//     where each segment is sorted once (`Sort(segv, ...)`) and summed.
//     Check that segment sizes sum to n, so the sorts total O(n log n);
//     the Python does the same `sorted(seg, reverse=True)` per run.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 44, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "SumSeq"],
//     "loop_depth": 1, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["Sort"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 1107_C. Brutality  (problem 2083, solution 2083_142)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
// 	n, k = map(int, input().split())
// 	a = list(map(int, input().split()))
// 	s = input().strip()
// 	last = s[0]
// 	seg = [a[0]]
// 	all = []
// 	for i in range(1, len(s)):
// 		if last == s[i]:
// 			seg.append(a[i])
// 		else:
// 			last = s[i]
// 			all.append(seg)
// 			seg = [a[i]]
// 	if seg:
// 		all.append(seg)
// 	ans = 0
// 	for seg in all:
// 		if k < len(seg):
// 			seg = sorted(seg, reverse = True)[:k]
// 		ans += sum(seg)
// 	print(ans)
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d: string) returns (output: string)
  requires |d| >= 1
  requires |c_list| == |d|
  requires b >= 0
{
  var k := b;
  var arr := c_list;
  var s := d;
  var last := s[0];
  var seg: seq<int> := [arr[0]];
  var allSegs: seq<seq<int>> := [];
  var i := 1;
  while i < |s|
    decreases |s| - i
  {
    if last == s[i] {
      seg := seg + [arr[i]];
    } else {
      last := s[i];
      allSegs := allSegs + [seg];
      seg := [arr[i]];
    }
    i := i + 1;
  }
  if |seg| > 0 {
    allSegs := allSegs + [seg];
  }
  var ans := 0;
  var si := 0;
  while si < |allSegs|
    decreases |allSegs| - si
  {
    var segv := allSegs[si];
    if k < |segv| {
      var sortedDesc := Sort(segv, (x: int, y: int) => x > y);
      segv := sortedDesc[..k];
    }
    ans := ans + SumSeq(segv);
    si := si + 1;
  }
  output := IntToString(ans);
}
