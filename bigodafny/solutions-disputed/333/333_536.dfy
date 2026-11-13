// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Python loops `while f`, each round scanning from index 1 to the
//     first vowel pair and rebuilding s by slicing, O(n**2); the Dafny
//     makes a single pass over `word` with `curr`, O(n), so the algorithm
//     was replaced.
//
//   how this label could be wrong, and what to check:
//     The Python is quadratic: it restarts its scan after every deletion
//     and rebuilds `s = s[:i] + s[i + 1:]`. Check that the Dafny instead
//     makes one pass with a `curr` tracker, which is O(n): the translation
//     reaches the same output by a faster algorithm.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 31, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 938_A. Word Correction  (problem 333, solution 333_536)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = list(input())
// glas = list('aoiyue')
// f = 1
// while f:
//     f = 0
//     for i in range(1, len(s)):
//         if s[i] in glas and s[i - 1] in glas:
//             f = 1
//             s = s[:i] + s[i + 1:]
//             break
// print(''.join(s))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, word: string) returns (output: string)
{
  if |word| == 0 {
    output := "\n";
    return;
  }
  var buf := new char[|word|];
  buf[0] := word[0];
  var j := 1;
  var curr := word[0];
  var i := 1;
  while i < |word|
    invariant 1 <= j <= i <= |word|
    decreases |word| - i
  {
    if IsVowelWC536(curr) && IsVowelWC536(word[i]) {
      // skip: this position gets removed in the fixed-point loop
    } else {
      buf[j] := word[i];
      j := j + 1;
      curr := word[i];
    }
    i := i + 1;
  }
  output := buf[0..j] + "\n";
}

predicate IsVowelWC536(c: char)
{
  c == 'a' || c == 'o' || c == 'i' || c == 'y' || c == 'u' || c == 'e'
}
