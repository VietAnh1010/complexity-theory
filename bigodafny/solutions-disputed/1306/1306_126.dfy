// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-fix
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     GroupCounts1306 calls CountOccur1306 and RemoveAll1306, each O(|a|),
//     once per distinct value, and the day loop runs up to maxC+1 times
//     each paying SumDiv1306 O(|counts|), so the worst case is quadratic
//     in |a_list|. The Python's while sum(x//i for x in a) >= n loop
//     likewise runs up to max-count times over all distinct counts, so the
//     label O(n) is wrong for both.
//
//   how this label could be wrong, and what to check:
//     The label assumes one linear pass, but the day loop may be O(max
//     count * distinct) and GroupCounts O(m * distinct), which is
//     quadratic in |a_list| when the list mixes one frequent value with
//     many distinct ones. Find GroupCounts1306 (CountOccur and RemoveAll
//     scanning a at every level) and the while loop calling
//     SumDiv1306(counts, day); compare with the Python's Counter and its
//     while sum(x//i for x in a) loop, and decide whether n in the label
//     means |a_list|.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 41, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "MaxSeq"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 4,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1011_B. Planning The Expedition  (problem 1306, solution 1306_126)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import*
// R=lambda:map(int,input().split())
// n,m=R()
// a=Counter(R()).values()
// i=1
// while sum(x//i for x in a)>=n:i+=1
// print(i-1)
//           
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountOccur1306(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[0] == v then 1 else 0) + CountOccur1306(a[1..], v)
}

function RemoveAll1306(a: seq<int>, v: int): seq<int>
  ensures |RemoveAll1306(a, v)| <= |a|
  decreases |a|
{
  if |a| == 0 then []
  else if a[0] == v then RemoveAll1306(a[1..], v)
  else [a[0]] + RemoveAll1306(a[1..], v)
}

function GroupCounts1306(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else [CountOccur1306(a, a[0])] + GroupCounts1306(RemoveAll1306(a[1..], a[0]))
}

function SumDiv1306(counts: seq<int>, day: int): int
  requires day > 0
  decreases |counts|
{
  if |counts| == 0 then 0
  else counts[0] / day + SumDiv1306(counts[1..], day)
}

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  var counts := GroupCounts1306(a_list);
  var maxC := if |counts| > 0 then MaxSeq(counts) else 0;
  var day := 1;
  while day <= maxC + 1 && SumDiv1306(counts, day) >= n
    decreases maxC + 2 - day
  {
    day := day + 1;
  }
  output := IntToString(day - 1);
}
