// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     l2 (and Dafny's `counts`) has size bounded by 100 distinct food
//     types, so SortInts/l2.sort cost O(1), but the while loop `i <=
//     maxC+1` and Python's `range(1,max(l2)+2)` scale with maxC which can
//     equal m when one type dominates, giving O(m) total for both, not O(m
//     log m).
//
//   how this label could be wrong, and what to check:
//     The label assumes l2.sort(reverse=True) dominates. Check that l2 has
//     at most 100 entries (one per distinct food type, capped by the
//     description's 1<=a_i<=100), making the sort O(1); the real cost is
//     the `for i in range(1,max(l2)+2)` loop, whose bound max(l2) can
//     reach m when one food type holds nearly all m packages. Confirm the
//     Dafny's `sorts` fact is empty (it is) and that MaxSeq plus the
//     while-loop bound scale with m, not with distinct count.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 48, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "MaxSeq"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 4,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1011_B. Planning The Expedition  (problem 1306, solution 1306_197)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// 
// n,m = list(map(int,input().split()))
// l = list(map(int,input().split()))
// 
// l2 = [y for x,y in Counter(l).items()]
// l2.sort(reverse=True)
// 
// #print(l2)
// 
// for i in range(1,max(l2)+2):
// 	if sum(int(x/i) for x in l2) < n:
// 		print(i-1)
// 		break
// else:
// 	print()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountOccur1306c(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[0] == v then 1 else 0) + CountOccur1306c(a[1..], v)
}

function RemoveAll1306c(a: seq<int>, v: int): seq<int>
  ensures |RemoveAll1306c(a, v)| <= |a|
  decreases |a|
{
  if |a| == 0 then []
  else if a[0] == v then RemoveAll1306c(a[1..], v)
  else [a[0]] + RemoveAll1306c(a[1..], v)
}

function GroupCounts1306c(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else [CountOccur1306c(a, a[0])] + GroupCounts1306c(RemoveAll1306c(a[1..], a[0]))
}

function SumDiv1306c(counts: seq<int>, day: int): int
  requires day > 0
  decreases |counts|
{
  if |counts| == 0 then 0
  else counts[0] / day + SumDiv1306c(counts[1..], day)
}

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  var counts := GroupCounts1306c(a_list);
  var maxC := if |counts| > 0 then MaxSeq(counts) else 0;
  var i := 1;
  var found := false;
  var result := 0;
  while i <= maxC + 1 && !found
    decreases (if found then 0 else 1), maxC + 2 - i
  {
    if SumDiv1306c(counts, i) < n {
      result := i - 1;
      found := true;
    } else {
      i := i + 1;
    }
  }
  output := if found then IntToString(result) else "";
}
