// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : main agent, override of labelaudit-r4-u01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Override of labelaudit-r4-u01's ok, which judged the old closed-form
//     translation; the Dafny now keeps the Python's search loop, which
//     runs up to MinSeq(d_list) - MaxSeq(c_list) times, a value term, so
//     the class is O(n + m + (q - p)); the Python pays the same.
//
//   how this label could be wrong, and what to check:
//     The label counts the two lists only. Check the restored `for x in
//     range(p, q)` loop: it steps x from max(right) toward min(wrong), a
//     difference of input VALUES. The proof in
//     solutions-proved/value-bounded/305/ carries that term.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 23, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "MaxSeq", "MinSeq"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 350_A. TL  (problem 305, solution 305_284)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// string = input()
// numbers = string.split()
// a = int(numbers[0])
// b = int(numbers[1])
// string = input()
// right = list(map(int, string.split()))
// string = input()
// wrong = list(map(int, string.split()))
// p = max(right)
// q = min(wrong)
// r = min(right)
// for x in range(p, q):
//     if r * 2 <= x:
//         print(x)
//         break
// else:
//     print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>, d_list: seq<int>) returns (output: string)
  requires |c_list| > 0
  requires |d_list| > 0
{
  var p := MaxSeq(c_list);
  var q := MinSeq(d_list);
  var r := MinSeq(c_list);
  // for x in range(p, q): if r * 2 <= x: print(x); break  else: print(-1)
  output := "-1";
  var x := p;
  var found := false;
  while x < q && !found
    decreases q - x, if found then 0 else 1
  {
    if r * 2 <= x {
      output := IntToString(x);
      found := true;
    } else {
      x := x + 1;
    }
  }
}


