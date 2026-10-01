// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r3d-04
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python runs `del l[0]` and `del l[-1]` in a while loop, and del
//     l[0] shifts the whole list, so it is O(n**2) as labelled, but the
//     Dafny walks two indices lo and hi over a_list without removing
//     anything, so one pass is O(n).
//
//   how this label could be wrong, and what to check:
//     The label matches the Python's deletion from the front of a list.
//     Check the Dafny `while lo <= hi && !stop` loop: it advances lo or
//     retreats hi and never builds a shorter sequence; if the Python's del
//     l[0] is considered quadratic, the translation avoided it by changing
//     the representation.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 26, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 999_A. Mishka and Contest  (problem 1470, solution 1470_325)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b = map(int,input().split())
// l= [int(i) for i in input().split()]
// 
// c=0
// while len(l)>0:
//     premier = l[0]
//     last= l[-1]
//     if premier<=b:
//         c+=1
//         del l[0]
//     elif last<=b:
//         c+=1
//         del l[-1]
//     else:
//         break
// 
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
  requires |a_list| == n
{
  var lo := 0;
  var hi := n - 1;
  var c := 0;
  var stop := false;
  while lo <= hi && !stop
    invariant 0 <= lo
    invariant hi <= n - 1
    decreases !stop, hi - lo + 1
  {
    if a_list[lo] <= k {
      c := c + 1;
      lo := lo + 1;
    } else if a_list[hi] <= k {
      c := c + 1;
      hi := hi - 1;
    } else {
      stop := true;
    }
  }
  output := IntToString(c);
}
