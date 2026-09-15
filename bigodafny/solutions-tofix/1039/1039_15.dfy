// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r2-05
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     firstPos := firstPos[x := i] and lastPos := lastPos[x := i] are seq
//     updates (`s[i:=v]`) executed inside loops over |nums|=n elements;
//     each seq update on a length-(n+1) seq copies the whole sequence,
//     turning two O(n) loops into O(n**2), while the Python performs the
//     equivalent first_pos[x]=i and last_pos[x]=i as O(1) in-place list
//     assignments, keeping the Python at the labelled O(n log n) via
//     last_pos.sort() and n bisect calls.
//
//   how this label could be wrong, and what to check:
//     The label assumes firstPos/lastPos updates are O(1) as Python list
//     assignment is. Open the two build loops and confirm the update is
//     `firstPos := firstPos[x := i]` / `lastPos := lastPos[x := i]` on a
//     seq<int> rather than a mutable array<int>; if it is a functional seq
//     update, each call copies n+1 entries and the two loops are
//     quadratic, so the Dafny (not the Python) needs the fix -- switching
//     firstPos/lastPos to array<int> would restore O(n log n).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 78, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInt",
//     "ParseIntFrom", "SplitWs"], "loop_depth": 2, "loops": 4,
//     "recursive_helpers": 3, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": true, "set_build_in_loop":
//     false, "sorts": ["SortInts"], "uses_map": false, "uses_multiset":
//     false, "uses_set": false}
// --------------------------------------------------------------------

// 1004_C. Sonya and Robots  (problem 1039, solution 1039_15)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import defaultdict
// from bisect import bisect
// 
// INF = 10**9
// 
// n = int(input())
// a = list(map(int, input().split()))
// 
// first_pos = [INF] * (n+1)
// for i, x in enumerate(a):
//     if first_pos[x] == INF:
//         first_pos[x] = i
//         
// last_pos = [-1] * (n+1)
// for i, x in enumerate(a):
//     last_pos[x] = i
// last_pos.sort()
// 
// total = 0
// for i, first in enumerate(first_pos):
//     total += len(last_pos) - bisect(last_pos, first)
// print(total)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then -ParseIntFrom(s, 1, 0)
  else ParseIntFrom(s, 0, 0)
}

function ParseIntList(ss: seq<string>): seq<int>
  decreases |ss|
{
  if |ss| == 0 then [] else [ParseInt(ss[0])] + ParseIntList(ss[1..])
}


method Solve(n_str: string, a_list_str: string) returns (output: string)
  requires var nums := ParseIntList(SplitWs(a_list_str));
           var n := ParseInt(n_str);
           n >= 0 && |nums| == n && forall k :: 0 <= k < |nums| ==> 1 <= nums[k] <= n
{
  var n := ParseInt(n_str);
  var nums := ParseIntList(SplitWs(a_list_str));
  var INF := 1000000000;
  var firstPos := seq(n + 1, _ => INF);
  var lastPos := seq(n + 1, _ => -1);
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |firstPos| == n + 1
    decreases |nums| - i
  {
    var x := nums[i];
    if firstPos[x] == INF {
      firstPos := firstPos[x := i];
    }
    i := i + 1;
  }
  i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |lastPos| == n + 1
    decreases |nums| - i
  {
    var x := nums[i];
    lastPos := lastPos[x := i];
    i := i + 1;
  }
  var sortedLast := SortInts(lastPos);
  var total := 0;
  i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant |firstPos| == n + 1
    decreases n - i
  {
    var first := firstPos[i];
    var lo := 0;
    var hi := |sortedLast|;
    while lo < hi
      invariant 0 <= lo <= hi <= |sortedLast|
      decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      if sortedLast[mid] <= first {
        lo := mid + 1;
      } else {
        hi := mid;
      }
    }
    total := total + (|sortedLast| - lo);
    i := i + 1;
  }
  output := IntToString(total);
}
