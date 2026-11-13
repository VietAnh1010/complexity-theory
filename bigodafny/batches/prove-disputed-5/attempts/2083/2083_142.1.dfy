// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(nlogn)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-d02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The first loop builds segments in O(n) with O(1) appends, then for
//     each segment Sort(segv, ...) costs O(len log len) and SumSeq O(len);
//     the lengths sum to |d|, so the total is O(nlogn), not O(n**2). The
//     Python's sorted(seg, reverse=True)[:k] and sum(seg) on the same
//     segments give the same class.
//
//   how this label could be wrong, and what to check:
//     The label assumes a quadratic cost, but the only superlinear work is
//     sorting segments. Check the Sort call on segv: the segment lengths
//     sum to n, so sorting each costs the sum of len*log(len), at most n
//     log n, and SumSeq of a segment is linear.
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

ghost function SumLens(ss: seq<seq<int>>): nat
{
  if |ss| == 0 then 0 else SumLens(ss[..|ss| - 1]) + |ss[|ss| - 1]|
}

lemma SumLensSnoc(ss: seq<seq<int>>, x: seq<int>)
  ensures SumLens(ss + [x]) == SumLens(ss) + |x|
{
  assert (ss + [x])[..|ss|] == ss;
}

lemma SumLensPrefix(ss: seq<seq<int>>, k: nat)
  requires k < |ss|
  ensures SumLens(ss[..k + 1]) == SumLens(ss[..k]) + |ss[k]|
{
  assert ss[..k + 1][..k] == ss[..k];
}

lemma NLogNSuper(a: nat, b: nat)
  ensures NLogN(a) + NLogN(b) <= NLogN(a + b)
{
  reveal NLogN();
  CeilLog2Monotone(a, a + b);
  CeilLog2Monotone(b, a + b);
  CostMulMono(a, CeilLog2(a) + 1, CeilLog2(a + b) + 1);
  CostMulMono(b, CeilLog2(b) + 1, CeilLog2(a + b) + 1);
  CostMulDistrib(a, b, a + b, CeilLog2(a + b) + 1);
}

method Solve(a: int, b: int, c_list: seq<int>, d: string) returns (output: string, ghost steps: nat)
  requires |d| >= 1
  requires |c_list| == |d|
  requires b >= 0
  ensures steps <= 2 * NLogN(|d|) + 22 * |d| + 20
{
  steps := 3;
  var k := b;
  var arr := c_list;
  var s := d;
  var last := s[0];
  var seg: seq<int> := [arr[0]];
  var allSegs: seq<seq<int>> := [];
  var i := 1;
  steps := steps + 3;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant SumLens(allSegs) + |seg| == i
    invariant |allSegs| < i
    invariant steps <= 6 + 10 * i
    decreases |s| - i
  {
    steps := steps + 10;
    if last == s[i] {
      seg := seg + [arr[i]];
    } else {
      last := s[i];
      SumLensSnoc(allSegs, seg);
      allSegs := allSegs + [seg];
      seg := [arr[i]];
    }
    i := i + 1;
  }
  if |seg| > 0 {
    SumLensSnoc(allSegs, seg);
    allSegs := allSegs + [seg];
  }
  steps := steps + 3;
  assert |allSegs| <= |s|;
  var ans := 0;
  var si := 0;
  ghost var tot := 0;
  assert allSegs[..0] == [];
  while si < |allSegs|
    invariant 0 <= si <= |allSegs|
    invariant tot == SumLens(allSegs[..si])
    invariant SumLens(allSegs) == |s|
    invariant steps <= 12 + 10 * |s| + 11 * si + tot + 2 * NLogN(tot)
    decreases |allSegs| - si
  {
    SumLensPrefix(allSegs, si);
    var segv := allSegs[si];
    ghost var len := |segv|;
    ghost var ntot := tot + len;
    NLogNSuper(tot, len);
    steps := steps + 11 + len;
    if k < |segv| {
      var sortedDesc := Sort(segv, (x: int, y: int) => x > y);
      segv := sortedDesc[..k];
      steps := steps + SortCost(len);
      SortCostNLogN(len);
    }
    ans := ans + SumSeq(segv);
    si := si + 1;
    tot := ntot;
  }
  assert allSegs[..|allSegs|] == allSegs;
  steps := steps + 3;
  output := IntToString(ans);
  steps := steps + Digits(ans);
}
