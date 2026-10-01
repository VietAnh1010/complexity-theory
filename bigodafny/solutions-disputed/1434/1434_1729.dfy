// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r3d-04
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     CountDistinct1434 calls ContainsInt1434b(xs[1..], xs[0]) at each
//     level, which is O(|xs|) per call, so it is O(|values|**2); the
//     Python tracks seen colours with `each not in dic`, an O(1) dict
//     lookup, so it is O(n). The linear dict test was replaced by a linear
//     scan.
//
//   how this label could be wrong, and what to check:
//     The problem fixes the input at exactly four integers, so every class
//     here is really constant. If the dataset takes |values| as the size,
//     the Dafny's membership scan inside the recursion is quadratic
//     against the Python's dict; open CountDistinct1434 and
//     ContainsInt1434b to check. If you treat four elements as a pinned
//     constant, the label O(n) itself is the error.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 21, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 0,
//     "loops": 0, "recursive_helpers": 2, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 228_A. Is your horseshoe on the other hoof?  (problem 1434, solution 1434_1729)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x = list(map(int, input().split()))
// dic ={}
// for each in x:
//     if each not in dic:
//         dic[each] = 0
//     dic[each] += 0
// h = len(dic)
// print(4 - h)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsInt1434b(xs: seq<int>, v: int): bool
  decreases |xs|
{
  if |xs| == 0 then false
  else if xs[0] == v then true
  else ContainsInt1434b(xs[1..], v)
}

function CountDistinct1434(xs: seq<int>): int
  decreases |xs|
{
  if |xs| == 0 then 0
  else if ContainsInt1434b(xs[1..], xs[0]) then CountDistinct1434(xs[1..])
  else 1 + CountDistinct1434(xs[1..])
}

method Solve(values: seq<int>) returns (output: string)
{
  var h := CountDistinct1434(values);
  output := IntToString(4 - h);
}
