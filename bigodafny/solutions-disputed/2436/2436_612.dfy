// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-18
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The while loop iterates i from 0 to |a|, doing one IsVowel612
//     comparison per character until a mismatch or the end of the string,
//     exactly mirroring Python's any((u in a)^(v in a) for u,v in
//     zip(x,y)) which also walks the full zipped string; both are O(n),
//     not O(1).
//
//   how this label could be wrong, and what to check:
//     The label claims constant time, but the while loop scans i from 0 up
//     to |a| comparing IsVowel612(a[i]) vs IsVowel612(b[i]) at each step;
//     open the loop and check it is bounded by |a| (string length up to
//     1000), a genuine size not a capped value, so this is a linear scan.
//     Compare against sibling 2436_325, whose near-identical algorithm on
//     the same problem is labelled O(n+m).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 30, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1111_A. Superhero Transformation  (problem 2436, solution 2436_612)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a={*'aeiou'}
// i=input
// x,y=i(),i()
// print('YNEOS'[len(x)!=len(y) or any((u in a)^(v in a) for u,v in zip(x,y))::2])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

predicate IsVowel612(c: char)
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

method Solve(a: string, b: string) returns (output: string)
{
  if |a| != |b| {
    output := "NO\n";
  } else {
    var i := 0;
    var mismatch := false;
    while i < |a| && !mismatch
      invariant 0 <= i <= |a|
      decreases |a| - i, (if mismatch then 0 else 1)
    {
      if IsVowel612(a[i]) != IsVowel612(b[i]) {
        mismatch := true;
      } else {
        i := i + 1;
      }
    }
    if mismatch {
      output := "NO\n";
    } else {
      output := "YES\n";
    }
  }
}
