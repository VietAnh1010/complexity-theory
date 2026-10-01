// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n**2)
//   cause          : label
//   confidence     : low
//   auditor        : labelaudit-r3-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop in Solve calls ContainsInt1434a on values[..i] for each i,
//     a recursive helper costing O(i), so the code is O(|values|**2) as
//     labelled, and the Python's `a[i] in a[:i]` is the same; but the
//     problem fixes |values| at 4.
//
//   how this label could be wrong, and what to check:
//     The label may be wrong because n is pinned: the statement says the
//     line holds exactly four integers s1..s4, so |values| is the constant
//     4 and the true class would be O(1). Read the Input section of the
//     description (four space-separated integers); if the dataset treats
//     the length of that single line as a variable n, the O(n**2) label
//     stands as is, and this row is then ok.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 21, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 228_A. Is your horseshoe on the other hoof?  (problem 1434, solution 1434_1616)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = list(map(int,input().split()))
// count = 0
// 
// for i in range(1,len(a)):
// 	if a[i] in a[:i]:
// 		count += 1
// print(count)	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsInt1434a(xs: seq<int>, v: int): bool
  decreases |xs|
{
  if |xs| == 0 then false
  else if xs[0] == v then true
  else ContainsInt1434a(xs[1..], v)
}

method Solve(values: seq<int>) returns (output: string)
{
  var count := 0;
  var i := 1;
  while i < |values|
    decreases |values| - i
  {
    if ContainsInt1434a(values[..i], values[i]) { count := count + 1; }
    i := i + 1;
  }
  output := IntToString(count);
}
