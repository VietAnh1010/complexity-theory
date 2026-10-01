// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n+m)
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r3-02
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny does only MaxSeq(c_list), MinSeq(d_list) and
//     MinSeq(c_list) plus O(1) arithmetic, so it is O(n+m) and equals the
//     label; the original Python additionally loops range(p, q) over a
//     value range, so the agreement comes from the closed-form `threshold`
//     replacing that loop, an algorithm replacement in the faster
//     direction.
//
//   how this label could be wrong, and what to check:
//     The label may describe a Python that pays a value-bounded loop while
//     the Dafny does not. The Python runs `for x in range(p, q)` until
//     `r*2 <= x`, up to about 2*min(a)-max(a) or q-p iterations, a value
//     term (<=100) beyond n+m; the Dafny replaced that scan by the closed
//     form `threshold := max(p, 2*r)`. Decide whether the label (measured
//     on the looping Python) should be called wrong or whether the Dafny's
//     O(n+m) is the class to record.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 12, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "MaxSeq", "MinSeq"],
//     "loop_depth": 0, "loops": 0, "recursive_helpers": 0,
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
  // The loop `for x in range(p, q): if r*2 <= x: print(x); break` picks the
  // smallest x in [p, q) with x >= 2*r -- since that condition is monotone in
  // x, it is exactly max(p, 2*r) when that value still lies below q.
  var threshold := if p >= 2 * r then p else 2 * r;
  output := if threshold < q then IntToString(threshold) else "-1";
}


