// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-20
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop over i runs k times, and each iteration calls
//     FindIndex(l, ...) three times, each an O(|l|) linear scan, plus
//     three seq updates l := l[idx := -1] costing O(|l|) each; with k up
//     to n/3 this is O(n**2), and the Python mirrors it with three
//     l.index() calls per iteration, also O(n**2).
//
//   how this label could be wrong, and what to check:
//     The label assumes the sort dominates, but the main loop calls
//     FindIndex (a linear scan over l) three times per iteration and runs
//     up to k = min(t1,t2,t3) <= n/3 iterations. Check that k can be
//     Theta(n) (e.g. n/3 children in each category) and that
//     FindIndex/list.index is O(n) per call; that makes both the Dafny and
//     Python O(n**2), with SortInts/l2.sort() not the bottleneck.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 82, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 2, "recursive_helpers": 4,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts":
//     ["SortInts"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 490_A. Team Olympiad  (problem 2610, solution 2610_1259)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input());t = 0;t2 = 0
// l = [int(i) for i in input().split()]
// l2 = l[:]
// l2.sort()
// #print('l2',l2)
// t1 = l.count(1)
// t2 = l.count(2)
// t3 = l.count(3)
// i1 = 0
// i2 = t1
// i3 = t1+t2
// print(min(t1,t2,t3))
// for i in range(min(t1,t2,t3)):
// #print('l2',l2)
// #	print(i1,i2,i3)
// 	print(l.index(l2[i1])+1,l.index(l2[i2])+1,l.index(l2[i3])+1)
// 	l[l.index(l2[i1])] = -1
// 	l[l.index(l2[i2])] = -1
// 	l[l.index(l2[i3])] = -1
// 	l2[i1] = -1;l2[i2] = -2;l2[i3] = -3
// 	
// 	
// 	i1+=1;i2+=1;i3+=1
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountEq(s: seq<int>, v: int): int
{
  if |s| == 0 then 0
  else (if s[0] == v then 1 else 0) + CountEq(s[1..], v)
}

lemma CountEqNonneg(s: seq<int>, v: int)
  ensures CountEq(s, v) >= 0
{
  if |s| == 0 {
  } else {
    CountEqNonneg(s[1..], v);
  }
}

lemma CountEqThreeBound(s: seq<int>, v1: int, v2: int, v3: int)
  requires v1 != v2 && v1 != v3 && v2 != v3
  ensures CountEq(s, v1) + CountEq(s, v2) + CountEq(s, v3) <= |s|
{
  if |s| == 0 {
  } else {
    CountEqThreeBound(s[1..], v1, v2, v3);
  }
}

method FindIndex(l: seq<int>, v: int) returns (idx: int)
  ensures 0 <= idx <= |l|
{
  idx := 0;
  while idx < |l| && l[idx] != v
    invariant 0 <= idx <= |l|
    decreases |l| - idx
  {
    idx := idx + 1;
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var l := a_list;
  var l2 := SortInts(a_list);
  var t1 := CountEq(a_list, 1);
  var t2 := CountEq(a_list, 2);
  var t3 := CountEq(a_list, 3);
  var i1 := 0;
  var i2 := t1;
  var i3 := t1 + t2;
  var k := t1;
  if t2 < k { k := t2; }
  if t3 < k { k := t3; }
  CountEqNonneg(a_list, 1);
  CountEqNonneg(a_list, 2);
  CountEqNonneg(a_list, 3);
  CountEqThreeBound(a_list, 1, 2, 3);
  var lines: seq<string> := [];
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant |lines| == i
    invariant i1 == i
    invariant i2 == t1 + i
    invariant i3 == t1 + t2 + i
    invariant |l| == |a_list|
    invariant k <= t1 && k <= t2 && k <= t3
    invariant t2 >= 0 && t3 >= 0
    invariant t1 + t2 + t3 <= |l2|
  {
    var idx1 := FindIndex(l, l2[i1]);
    var idx2 := FindIndex(l, l2[i2]);
    var idx3 := FindIndex(l, l2[i3]);
    lines := lines + [IntToString(idx1 + 1) + " " + IntToString(idx2 + 1) + " " + IntToString(idx3 + 1)];
    if idx1 < |l| { l := l[idx1 := -1]; }
    if idx2 < |l| { l := l[idx2 := -1]; }
    if idx3 < |l| { l := l[idx3 := -1]; }
    i1 := i1 + 1;
    i2 := i2 + 1;
    i3 := i3 + 1;
    i := i + 1;
  }
  output := IntToString(k) + "\n";
  if |lines| > 0 {
    output := output + Join(lines, "\n") + "\n";
  }
}
