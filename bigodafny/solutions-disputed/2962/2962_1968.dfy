// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : main agent, override of labelaudit-r4-s05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Override of labelaudit-r4-s05's unsure: for each letter of the two
//     names the code scans and deletes from the pile jumbled_name, a
//     different input, so the cost is (|first|+|second|) times |jumbled|,
//     O(n*m) by the naming rule; the Python's `in m` and remove on the
//     pile pay the same.
//
//   how this label could be wrong, and what to check:
//     The label squares one size, but the code multiplies two: the names'
//     letters and the pile. Check the proof bound
//     (|first_name|+|second_name|)*(3*|jumbled_name|+7): the pile is a
//     separate input, so its length is a second size.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 38, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 2, "loops": 2,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 3, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 141_A. Amusing Joke  (problem 2962, solution 2962_1968)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=input()
// l=input()
// m=input()
// a=len(n)+len(l)
// c=0
// n=list(n)+list(l)
// m=list(m)
// d=[]
// d=d+m
// for i in range(len(n)):
//     if n[i] not in m:
//         c=1
//         break
//     else:
//         d.remove(n[i])
//         m.remove(n[i])
// if c==1:
//     print("NO")
// elif len(d)!=0:
//     print("NO")
// else:
//     print("YES")
//             
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(first_name: seq<string>, second_name: seq<string>, jumbled_name: seq<string>) returns (output: string)
{
  var need := first_name + second_name;
  var remaining := jumbled_name;
  var c := 0;
  var i := 0;
  while i < |need| && c == 0
    invariant 0 <= i <= |need|
    decreases |need| - i
  {
    var ch := need[i];
    var idx := -1;
    var j := 0;
    while j < |remaining|
      invariant 0 <= j <= |remaining|
      invariant idx == -1 || (0 <= idx < j && remaining[idx] == ch)
      decreases |remaining| - j
    {
      if idx == -1 && remaining[j] == ch { idx := j; }
      j := j + 1;
    }
    if idx == -1 {
      c := 1;
    } else {
      remaining := remaining[..idx] + remaining[idx + 1..];
    }
    i := i + 1;
  }
  if c == 1 {
    output := "NO";
  } else if |remaining| != 0 {
    output := "NO";
  } else {
    output := "YES";
  }
}
