// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-10
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop over n days calls MinSeq(arr[lo..hi]) with hi-lo up to
//     b+c+1, so each iteration costs the window width (values x and y),
//     giving O(n*(x+y)); the Python min() over the same slice pays the
//     same, and the statement cap x,y<=7 does not make it constant.
//
//   how this label could be wrong, and what to check:
//     The label assumes each iteration is O(1), but the window width x+y+1
//     is an input value. Check that MinSeq(arr[lo..hi]) in the Dafny and
//     min(arr[i-x:i+y+1]) in the Python both scan a window whose length is
//     set by the values x and y read from the first line; if the window
//     were a fixed literal the label would stand.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 37, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "MinSeq"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1199_A. City Day  (problem 1820, solution 1820_180)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n , x , y = map(int,input().split())
// arr = list(map(int,input().split()))
// 
// for i in range(n):
//     if i >= x :
//         if arr[i] == min(arr[i - x : i + y + 1]):
//             print(i + 1 )
//             break
//     else:
//         if arr[i] == min(arr[0 : i + y +1]):
//             print(i + 1 )
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
  requires a <= |d_list|
  requires b >= 0
  requires c >= 0
{
  var n := a;
  var x := b;
  var y := c;
  var arr := d_list;
  var i := 0;
  var found := false;
  var result := 0;
  while i < n && !found
    invariant 0 <= i
    decreases !found, n - i
  {
    var lo := if i >= x then i - x else 0;
    var hi := i + y + 1;
    if hi > |arr| { hi := |arr|; }
    assert lo <= i;
    assert hi >= i + 1;
    var m := MinSeq(arr[lo..hi]);
    if arr[i] == m {
      result := i + 1;
      found := true;
    } else {
      i := i + 1;
    }
  }
  if found {
    output := IntToString(result);
  } else {
    output := "";
  }
}
