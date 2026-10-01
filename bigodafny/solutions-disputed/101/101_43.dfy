// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n)
//   cause          : harness
//   confidence     : high
//   auditor        : labelaudit-r3d-01
//
//   Both artifacts are right. The Python pays to parse stdin and
//   BigOBench profiled the whole script; the Dafny's Solve receives the
//   inputs already parsed, so that cost is outside the measured method.
//   Nothing to repair -- document it.
//
//   evidence:
//     Solve reads only b_list[0] and otherwise does CountZeros and two
//     loops over a_list, so it is O(n); the Python's O(n+m) comes from
//     parsing the whole b line, which the Dafny receives pre-parsed.
//
//   how this label could be wrong, and what to check:
//     The label includes m for the length of b, but the Dafny never scans
//     b_list. Check Solve: it reads only b_list[0] after
//     CountZeros(a_list) and two loops over |a|; the Python parses all of
//     b with list(map(int, input().split())), which is where the m term
//     comes from.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 40, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 2,
//     "recursive_helpers": 1, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": true, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 814_A. An abandoned sentiment from past  (problem 101, solution 101_43)
// time complexity: O(n+m)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input = sys.stdin.readline
// N, K = map(int, input().split())
// a = list(map(int, input().split()))
// b = list(map(int, input().split()))
// if a.count(0) > 1: print("Yes")
// else:
//   for i in range(N):
//     if a[i] == 0:
//       a[i] = b[0]
//   for i in range(N - 1):
//     if a[i + 1] <= a[i]:
//       print("Yes")
//       break
//   else: print("No")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  var cnt := CountZeros(a_list);
  if cnt > 1 {
    output := "Yes\n";
  } else {
    var a := a_list;
    var bv := if |b_list| > 0 then b_list[0] else 0;
    var i := 0;
    while i < |a|
      invariant 0 <= i <= |a|
      decreases |a| - i
    {
      if a[i] == 0 {
        a := a[i := bv];
      }
      i := i + 1;
    }
    var found := false;
    var j := 0;
    while j < |a| - 1 && !found
      invariant 0 <= j <= |a|
      decreases |a| - j
    {
      if a[j+1] <= a[j] {
        found := true;
      }
      j := j + 1;
    }
    output := if found then "Yes\n" else "No\n";
  }
}

function CountZeros(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == 0 then 1 else 0) + CountZeros(s[1..])
}
