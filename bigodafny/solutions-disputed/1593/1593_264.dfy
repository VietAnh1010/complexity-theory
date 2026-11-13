// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny's nested loops compare `s[j..j+2] == cur` for every pair
//     (i, j), O(n**2); the Python builds the list of n - 1 bigrams and
//     counts them with `Counter`, O(n), so the translation is a class
//     slower.
//
//   how this label could be wrong, and what to check:
//     The Python counts all bigrams with one `Counter` pass, O(n) as
//     labelled. Check the Dafny: for every position i it rescans the whole
//     string in an inner `while j < n - 1` loop, O(n**2). A map count
//     would restore O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 30, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 2, "loops": 2,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 977_B. Two-gram  (problem 1593, solution 1593_264)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// l = []
// from collections import Counter
// for i in range(0,len(s)-1):
//     l.append(s[i:i+2])
// l = Counter(l)
// l = dict(l)
// max = 0
// for word in l:
//     if l[word] > max:
//         max = l[word]
//         string = word
// 
// print(string)
// 
//         
// 
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var n := |s|;
  var bestCount := 0;
  var bestStr := "";
  var i := 0;
  while i < n - 1
    decreases n - 1 - i
  {
    var cur := s[i..i+2];
    var cnt := 0;
    var j := 0;
    while j < n - 1
      decreases n - 1 - j
    {
      if s[j..j+2] == cur {
        cnt := cnt + 1;
      }
      j := j + 1;
    }
    if cnt > bestCount {
      bestCount := cnt;
      bestStr := cur;
    }
    i := i + 1;
  }
  output := bestStr;
}
