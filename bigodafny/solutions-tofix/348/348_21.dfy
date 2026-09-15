// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-03
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     ContainsInt(source, s) linearly scans the seq `source` (length up to
//     idx) on every loop iteration to emulate Python's `s in source`, so
//     total cost is O(n**2); Python uses set() with O(1) average
//     membership and add(), so the Python is genuinely O(n) as labelled
//     and the seq-based translation is the defect.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 38, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 24_A. Ring road  (problem 348, solution 348_21)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// source=set()
// dest=set()
// c1=0
// c2=0
// for i in range(int(input())):
//     s,d,w=map(int,input().split())
//     if s in source or d in dest:
//         c1=c1+w
//         s,d=d,s
//     else:
//         c2=c2+w
//     source.add(s)
//     dest.add(d)
// print(min(c1,c2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsInt(xs: seq<int>, x: int): bool
  decreases |xs|
{
  if |xs| == 0 then false
  else if xs[0] == x then true
  else ContainsInt(xs[1..], x)
}

method Solve(n: int, v_list: seq<seq<int>>) returns (output: string)
  requires forall k :: 0 <= k < |v_list| ==> |v_list[k]| >= 3
{
  var source: seq<int> := [];
  var dest: seq<int> := [];
  var c1 := 0;
  var c2 := 0;
  var idx := 0;
  while idx < |v_list|
    invariant 0 <= idx <= |v_list|
    decreases |v_list| - idx
  {
    var s := v_list[idx][0];
    var d := v_list[idx][1];
    var w := v_list[idx][2];
    if ContainsInt(source, s) || ContainsInt(dest, d) {
      c1 := c1 + w;
      var tmp := s;
      s := d;
      d := tmp;
    } else {
      c2 := c2 + w;
    }
    source := source + [s];
    dest := dest + [d];
    idx := idx + 1;
  }
  output := IntToString(if c1 < c2 then c1 else c2);
}
