// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r2-05
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     This sibling of 1027_207 keeps the same nested-loop dedup: `while
//     j<|dxs|` scans the whole accumulated slope list for each of the n
//     points, an O(n**2) construct; but its Python replaces the linear
//     scan with `if m not in slope` on a dict keyed by slope, an
//     O(1)-average membership test, making the Python genuinely O(n) as
//     labelled.
//
//   how this label could be wrong, and what to check:
//     The label O(n) is claimed to match the Dafny, but check whether the
//     inner `while j < |dxs|` loop is bounded by a constant or by the
//     growing list dxs; if dxs can hold up to n distinct slopes (e.g. all
//     points at different angles from the gun), that inner loop's total
//     work across all outer iterations is O(n**2), the same shape as
//     1027_207's Dafny. Compare directly against 1027_207's inner loop,
//     translated the same way and already labelled O(n**2) -- if the two
//     Dafny loop bodies are structurally identical, one of the two labels
//     must be wrong, and the Python source (dict membership vs manual
//     scan) settles which one.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 43, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     true, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 514_B. Han Solo and Lazer Gun  (problem 1027, solution 1027_458)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, x1, y1 = [int(s) for s in input().split()] 
// slope = {}
// shoot=0
// for i in range(n):
//     x2,y2=[int(s) for s in input().split()]
//     if(x2-x1)==0:
//         m="a"
//     else:
//         m = (y2-y1)/(x2-x1)
//     
//     if m not in slope:
//         shoot+=1
//         slope[m] = 0
// print(shoot)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<(int, int)>) returns (output: string)
{
  var seenVertical := false;
  var dxs: seq<int> := [];
  var dys: seq<int> := [];
  var shoot := 0;
  var i := 0;
  while i < |d_list|
    invariant 0 <= i <= |d_list|
    invariant |dxs| == |dys|
    decreases |d_list| - i
  {
    var dx := d_list[i].0 - b;
    var dy := d_list[i].1 - c;
    if dx == 0 {
      if !seenVertical {
        seenVertical := true;
        shoot := shoot + 1;
      }
    } else {
      var found := false;
      var j := 0;
      while j < |dxs|
        invariant 0 <= j <= |dxs|
        decreases |dxs| - j
      {
        if dys[j] * dx == dy * dxs[j] {
          found := true;
        }
        j := j + 1;
      }
      if !found {
        dxs := dxs + [dx];
        dys := dys + [dy];
        shoot := shoot + 1;
      }
    }
    i := i + 1;
  }
  output := IntToString(shoot);
}
