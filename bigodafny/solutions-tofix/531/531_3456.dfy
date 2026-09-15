// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-04
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop is bounded by the literal constant 5 (i<5), not by
//     any size parameter n, and AllSame3456/IndexOf1From3456 run over a
//     fixed-width row, so the whole method is O(1); Python's for i in
//     range(0,5) loop with break is the same fixed 5-iteration scan, also
//     O(1).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 40, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 263_A. Beautiful Matrix  (problem 531, solution 531_3456)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// col=row=1
// 
// for i in range (0,5):
//     a=list(input().split())
//     if(len(set(a))==1): row+=1
//     else: col=a.index('1')+1 ; break
// 
// print(abs(3-row)+abs(3-col))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(matrix: seq<seq<int>>) returns (output: string)
  requires |matrix| >= 5
{
  var row := 1;
  var col := 1;
  var i := 0;
  var found := false;
  while i < 5 && !found
    invariant 0 <= i <= 5
    decreases 5 - i
  {
    var r := matrix[i];
    if AllSame3456(r) {
      row := row + 1;
    } else {
      col := IndexOf1From3456(r, 0) + 1;
      found := true;
    }
    i := i + 1;
  }
  output := IntToString(Abs3456(3 - row) + Abs3456(3 - col)) + "\n";
}

function AllSame3456(r: seq<int>): bool
{
  forall k :: 0 <= k < |r| ==> r[k] == r[0]
}

function IndexOf1From3456(r: seq<int>, i: int): int
  requires 0 <= i <= |r|
  decreases |r| - i
{
  if i >= |r| then -1
  else if r[i] == 1 then i
  else IndexOf1From3456(r, i + 1)
}

function Abs3456(x: int): int
{
  if x < 0 then -x else x
}
