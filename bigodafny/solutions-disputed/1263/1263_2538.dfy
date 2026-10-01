// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-06
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The outer loop is over n tests, but the inner loop runs ln =
//     |IntToString(a_list[t])| times, the digit count of each element,
//     with Repeat of up to ln-i-1 zeros and a Join per test, so cost is
//     O(sum over tests of digits squared), a value term the label O(n)
//     omits. The Python iterates range(len(n)) over the same digit string
//     and builds '0'*(ln-i-1), so it pays the same.
//
//   how this label could be wrong, and what to check:
//     The label counts only the t test cases, but each test also pays per
//     digit of its value. Check Solve: ln := |IntToString(v)| bounds the
//     inner while loop, and Repeat("0", ln-i-1) plus Join(lst) add more;
//     compare with the Python's len(n) loop on the digit string. If every
//     test value is known to be a fixed small width the label would stand,
//     but the statement only caps n at 10^4, which is a cap and not a
//     source literal.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 32, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "Repeat"],
//     "loop_depth": 2, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1352_A. Sum of Round Numbers  (problem 1263, solution 1263_2538)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// for _ in range(t):
//     n = input()
//     k = len(n.replace('0', ''))
//     print(k)
//     ln = len(n)
//     lst = [n[i]+'0'*(ln-i-1) for i in range(ln) if n[i] != '0']
//     print(*lst)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
{
{

  var results: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    decreases n - t
  {
    var v := a_list[t];
    var s := IntToString(v);
    var ln := |s|;
    var lst: seq<string> := [];
    var i := 0;
    while i < ln
      invariant 0 <= i <= ln
      decreases ln - i
    {
      if s[i] != '0' {
        lst := lst + [[s[i]] + Repeat("0", ln - i - 1)];
      }
      i := i + 1;
    }
    results := results + [IntToString(|lst|), Join(lst, " ")];
    t := t + 1;
  }
  output := Join(results, "\n");
}
}
