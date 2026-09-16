// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-20
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both while loops in CheckMancala and the outer loop in Solve are
//     bounded by the literal constant 14, not by |values| or any variable;
//     the board size is fixed by the problem statement ("The only line
//     contains 14 integers"), so the whole method does O(1) work
//     regardless of any n, and the Python check() function is likewise
//     called at most 14 times over a fixed 14-element list.
//
//   how this label could be wrong, and what to check:
//     The label assumes some dimension named n grows, but the signature is
//     Solve(values: seq<int>) requiring |values| == 14 and the board is
//     always exactly 14 holes per the description ("The only line contains
//     14 integers"). Check that every loop bound in Solve and CheckMancala
//     is the literal 14, never |values| or a derived count, confirming
//     there is no scaling variable at all.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 55, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 3, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 975_B. Mancala  (problem 2639, solution 2639_117)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = list(map(int, input().split()))
// 
// def check(a):
//     a = a[:]
//     x = a[0]
//     a[0] = 0
//     for i in range(1, 14):
//         a[i] += max(0, (x+14-i) // 14)
//     a[0] = max(0, x // 14)
//     return sum((x if x % 2 == 0 else 0 for x in a))
// 
// print(max((check(a[i:] + a[:i]) for i in range(14) if a[i] > 0)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method CheckMancala(b: seq<int>) returns (result: int)
  requires |b| == 14
{
  var x := b[0];
  var c := b[0 := 0];
  var i := 1;
  while i < 14
    invariant 1 <= i <= 14
    invariant |c| == 14
    decreases 14 - i
  {
    var add := (x + 14 - i) / 14;
    if add < 0 { add := 0; }
    c := c[i := c[i] + add];
    i := i + 1;
  }
  var z := x / 14;
  if z < 0 { z := 0; }
  c := c[0 := z];
  var s := 0;
  i := 0;
  while i < 14
    invariant 0 <= i <= 14
    invariant |c| == 14
    decreases 14 - i
  {
    if c[i] % 2 == 0 { s := s + c[i]; }
    i := i + 1;
  }
  result := s;
}

method Solve(values: seq<int>) returns (output: string)
  requires |values| == 14
{
  var best := 0;
  var found := false;
  var i := 0;
  while i < 14
    invariant 0 <= i <= 14
    decreases 14 - i
  {
    if values[i] > 0 {
      var rot := seq(14, j requires 0 <= j < 14 => values[(i + j) % 14]);
      var r := CheckMancala(rot);
      if !found || r > best {
        best := r;
        found := true;
      }
    }
    i := i + 1;
  }
  output := IntToString(best);
}
