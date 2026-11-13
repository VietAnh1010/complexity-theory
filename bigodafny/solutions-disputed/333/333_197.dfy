// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : both
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Dafny keeps each character not preceded by a vowel pair in one
//     loop over `word`, O(n), with no sort and no deletion; the Python
//     sorts `remove` and pops each index from the list, which shifts the
//     tail and reaches O(n**2), so neither matches O(nlogn).
//
//   how this label could be wrong, and what to check:
//     The label counts only `remove.sort`. The Python then calls
//     `word.pop(r)` per index, and a pop shifts every later element: a
//     vowel run followed by many consonants makes that O(n**2). The Dafny
//     does neither, copying kept characters into `buf` in one pass. Check
//     the pops' shift cost and the Dafny's single loop.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 28, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 938_A. Word Correction  (problem 333, solution 333_197)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #/usr/bin/python3
// 
// # MC721A
// # 27 de março de 2020
// # Rogério Meirelles - RA160245
// 
// n = int(input())
// word = [char for char in input()]
// vowels = ['a', 'e', 'i', 'o', 'u', 'y']
// remove = []
// 
// for i in range(1, n):
//     if word[i] in vowels and word[i-1] in vowels:
//         remove.append(i)
// 
// remove.sort(reverse=True)
// 
// for r in remove:
//     word.pop(r)
// 
// print(''.join(word))
// 	 	 	 	 	   	 	 	    	     			
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
  var i := 1;
  while i < |word|
    invariant 1 <= j <= i <= |word|
    decreases |word| - i
  {
    if !(IsVowelWC197(word[i]) && IsVowelWC197(word[i-1])) {
      buf[j] := word[i];
      j := j + 1;
    }
    i := i + 1;
  }
  output := buf[0..j] + "\n";
}

predicate IsVowelWC197(c: char)
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y'
}
