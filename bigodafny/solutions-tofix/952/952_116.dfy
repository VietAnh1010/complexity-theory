// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r2-05
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     ReverseInts(arr) recurses via `ReverseInts(s[1..]) + [s[0]]`, the
//     identical slice-and-concatenate-at-every-level shape flagged for
//     ReverseSeq in 888_6, which copies O(current length) per level; since
//     |arr| can be as large as n (a fully increasing run of a_list), this
//     call alone is O(n**2), while the Python builds the answer with O(1)
//     `arr.append` calls and a single O(n) `arr[::-1]` slice.
//
//   how this label could be wrong, and what to check:
//     The label assumes the final reversal costs O(n) the way Python's
//     arr[::-1] does. Open ReverseInts and confirm it is defined as
//     `ReverseInts(s[1..]) + [s[0]]`; if the backend does not special-case
//     that concatenation the way it does a flat loop's `s := s + [x]`,
//     each level copies the accumulated result and the call is
//     O(|arr|**2). Also check how large |arr| can get -- if a single test
//     can make a_list one long increasing run, |arr| ~= n and the
//     quadratic term dominates, so the label is too low; if |arr| is
//     provably small for every valid input, the label could still stand.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 57, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "JoinInts"],
//     "loop_depth": 1, "loops": 3, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": true, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 977_F. Consecutive Subsequence  (problem 952, solution 952_116)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// dc = dict()
// for x in a:
//     dc[x] = max(dc.get(x, 0), dc.get(x - 1, 0) + 1)
// ans = 0
// mx = 0
// for x in dc.keys():
//     if dc[x] > mx:
//         mx = dc[x]
//         ans = x
// arr = []
// for i in range(n - 1, -1, -1):
//     if a[i] == ans:
//         ans -= 1
//         arr.append(i + 1)
// print(len(arr))
// print(*arr[::-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
{
  var dc: map<int, int> := map[];
  var order: seq<int> := [];
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant forall v :: v in order ==> v in dc
    decreases |a_list| - idx
  {
    var x := a_list[idx];
    var cur := if x in dc then dc[x] else 0;
    var prevChain := if (x - 1) in dc then dc[x - 1] else 0;
    var newval := if cur > prevChain + 1 then cur else prevChain + 1;
    if !(x in dc) {
      order := order + [x];
    }
    dc := dc[x := newval];
    idx := idx + 1;
  }
  var ans := 0;
  var mx := 0;
  var k := 0;
  while k < |order|
    invariant 0 <= k <= |order|
    invariant forall v :: v in order ==> v in dc
    decreases |order| - k
  {
    var xx := order[k];
    if dc[xx] > mx {
      mx := dc[xx];
      ans := xx;
    }
    k := k + 1;
  }
  var arr: seq<int> := [];
  var i := n - 1;
  while i >= 0
    invariant -1 <= i <= n - 1
    decreases i + 1
  {
    if a_list[i] == ans {
      ans := ans - 1;
      arr := arr + [i + 1];
    }
    i := i - 1;
  }
  output := IntToString(|arr|) + "\n" + JoinInts(ReverseInts(arr), " ") + "\n";
}

function ReverseInts(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [] else ReverseInts(s[1..]) + [s[0]]
}
