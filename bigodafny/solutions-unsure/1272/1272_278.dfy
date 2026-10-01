// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(nlogn)
//   cause          : label
//   confidence     : low
//   auditor        : labelaudit-r3-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Sort by length is O(n log n) and the Python arr.sort(key=len)
//     matches, but the following loop calls Contains1272b once per
//     adjacent pair at O(|hay|*|needle|) each, a string-length term the
//     label omits; the Python's str.find is C-level so its practical cost
//     is lower. I lean toward the label standing under the
//     fixed-length-cap reading.
//
//   how this label could be wrong, and what to check:
//     The label names only n, but each adjacent pair runs Contains1272b,
//     whose naive search costs |hay|*|needle|. Open Contains1272b and
//     ContainsFrom1272b to confirm the slice comparison is linear in
//     |needle| at every position; if string length is treated as fixed
//     (the statement caps it at 100) the Sort dominates and the label
//     stands, otherwise it is O(n log n + n*L**2) and mismatched.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 40, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     2, "recursive_helpers": 2, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": ["Sort"], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 988_B. Substrings Sort  (problem 1272, solution 1272_278)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def solve(arr):
//     for i in range(0,len(arr)-1):
//         x = arr[i+1].find(arr[i])
//        # print(x)
//         if x == -1:
//             return 0
//     return 1
// n=int(input())
// arr = []
// while n:
//     s = str(input())
//     arr.append(s)
//     n=n-1
// arr.sort(key=len)
// flag = solve(arr)
// if flag:
//     print("YES")
//     for i in arr:
//         print(i)
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsFrom1272b(hay: string, needle: string, pos: nat): bool
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  if pos + |needle| > |hay| then false
  else if hay[pos..pos+|needle|] == needle then true
  else ContainsFrom1272b(hay, needle, pos + 1)
}

function Contains1272b(hay: string, needle: string): bool
{
  |needle| == 0 || ContainsFrom1272b(hay, needle, 0)
}

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var arr := Sort(strings, (x: string, y: string) => |x| < |y|);
  var flag := true;
  var i := 0;
  while i < |arr| - 1
    decreases |arr| - 1 - i
  {
    if !Contains1272b(arr[i+1], arr[i]) { flag := false; }
    i := i + 1;
  }
  if flag {
    var lines: seq<string> := ["YES"];
    var m := 0;
    while m < |arr|
      decreases |arr| - m
    {
      lines := lines + [arr[m]];
      m := m + 1;
    }
    output := Join(lines, "\n");
  } else {
    output := "NO";
  }
}
