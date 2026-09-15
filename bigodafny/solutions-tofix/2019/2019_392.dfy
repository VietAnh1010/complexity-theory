// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-15
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve takes scalar a, scalar b (k), and one sequence c_list parsed
//     into v; the while loop runs over |v| once with O(1) work per
//     iteration, and there is no second collection to give an m term.
//
//   how this label could be wrong, and what to check:
//     The label posits a second sized dimension m, but Solve's signature
//     has only scalars a and b plus one sequence c_list; check the
//     signature for any second seq/array parameter. There is none, so the
//     single while loop over |v| makes this O(n), and the Python's single
//     for loop over enumerate(...) confirms it.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 25, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInts"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 839_A. Arya and Bran  (problem 2019, solution 2019_392)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// _, k = map(int, input().split())
// 
// acc = 0
// result = -1
// for i, v in enumerate(map(int, input().split())):
//     acc += v
//     d = min(acc, 8) 
//     k -= d
//     acc -= d
//     if k <= 0:
//         result = i + 1
//         break
// 
// print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<string>) returns (output: string)
{
  var k := b;
  var v := ParseInts(c_list);
  var acc := 0;
  var result := -1;
  var i := 0;
  var stopped := false;
  while i < |v| && !stopped
    decreases |v| - i
  {
    acc := acc + v[i];
    var d := if acc < 8 then acc else 8;
    k := k - d;
    acc := acc - d;
    if k <= 0 {
      result := i + 1;
      stopped := true;
    }
    i := i + 1;
  }
  output := IntToString(result);
}
