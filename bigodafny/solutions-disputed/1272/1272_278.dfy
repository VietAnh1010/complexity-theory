// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-u01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve sorts n strings by |x| < |y| in O(n log n) and then makes n-1
//     substring checks each scanning the haystack string, O(m) per check,
//     so O(n log n + n*m); the Python's arr.sort(key=len) and find per
//     adjacent pair pay the same, so the label omits the width.
//
//   how this label could be wrong, and what to check:
//     The label O(nlogn) counts only the Sort of the n strings by length.
//     Find Contains1272b(arr[i+1], arr[i]) in the loop over arr:
//     ContainsFrom1272b walks every position of the haystack, so each of
//     n-1 pairs costs a width m. If you consider m negligible the label
//     stands; otherwise the class is O(n log n + n*m).
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
