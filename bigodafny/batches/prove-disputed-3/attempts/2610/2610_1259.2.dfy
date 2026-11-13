// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop runs k = min counts times, and each iteration does three
//     FindIndex linear scans over l; the matched slots are replaced by -1,
//     so the scan start drifts and total work is Theta(n**2) beyond the
//     O(n log n) SortInts. The Python's three `l.index(...)` calls per
//     round are equally linear, so the label is wrong for both.
//
//   how this label could be wrong, and what to check:
//     The label assumes sort-dominated work, but each of up to n/3 team
//     iterations calls FindIndex three times, each a linear scan. Try
//     input with all 1s first, then 2s, then 3s: the first match of each
//     value moves right by one per round, so scans are about n/3 to n
//     long.
//
//   structural facts (deterministic, from label_audit.py):
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

method FindIndex(l: seq<int>, v: int) returns (idx: int, ghost steps: nat)
  ensures 0 <= idx <= |l|
  ensures steps <= 4 * |l| + 2
{
  steps := 1;
  idx := 0;
  while idx < |l| && l[idx] != v
    invariant 0 <= idx <= |l|
    invariant steps <= 4 * idx + 1
    decreases |l| - idx
  {
    idx := idx + 1;
    steps := steps + 4;
  }
  steps := steps + 1;
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|a_list|) + 3 * |a_list| + |a_list| * (12 * |a_list| + 30) + 4 * |output| + 40
{
  steps := 1;
  var l := a_list;
  var l2 := SortInts(a_list);
  steps := steps + SortCost(|a_list|);
  SortCostWithin(|a_list|, |a_list|);
  var t1 := CountEq(a_list, 1);
  var t2 := CountEq(a_list, 2);
  var t3 := CountEq(a_list, 3);
  steps := steps + 3 * (|a_list| + 1);
  var i1 := 0;
  var i2 := t1;
  var i3 := t1 + t2;
  var k := t1;
  if t2 < k { k := t2; }
  if t3 < k { k := t3; }
  steps := steps + 6;
  CountEqNonneg(a_list, 1);
  CountEqNonneg(a_list, 2);
  CountEqNonneg(a_list, 3);
  CountEqThreeBound(a_list, 1, 2, 3);
  var lines: seq<string> := [];
  var i := 0;
  ghost var K := 12 * |a_list| + 30;
  ghost var base := steps;
  assert base <= SortCost(|a_list|) + 3 * |a_list| + 10;
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
    invariant steps <= base + i * K + 2 * SumLen(lines)
  {
    var idx1, s1 := FindIndex(l, l2[i1]);
    var idx2, s2 := FindIndex(l, l2[i2]);
    var idx3, s3 := FindIndex(l, l2[i3]);
    IntToStringDigits(idx1 + 1);
    IntToStringDigits(idx2 + 1);
    IntToStringDigits(idx3 + 1);
    var line := IntToString(idx1 + 1) + " " + IntToString(idx2 + 1) + " " + IntToString(idx3 + 1);
    SumLenSnoc(lines, line);
    lines := lines + [line];
    if idx1 < |l| { l := l[idx1 := -1]; }
    if idx2 < |l| { l := l[idx2 := -1]; }
    if idx3 < |l| { l := l[idx3 := -1]; }
    i1 := i1 + 1;
    i2 := i2 + 1;
    i3 := i3 + 1;
    i := i + 1;
    steps := steps + s1 + s2 + s3 + 30 + 2 * |line|;
    CostMulDistrib(i - 1, 1, i, K);
  }
  CostMulMonoLeft(k, |a_list|, K);
  output := IntToString(k) + "\n";
  IntToStringDigits(k);
  steps := steps + Digits(k) + 2;
  if |lines| > 0 {
    JoinLen(lines, "\n");
    var j := Join(lines, "\n");
    steps := steps + SumLen(lines) + |lines| + |j| + 1;
    output := output + j + "\n";
  }
}
