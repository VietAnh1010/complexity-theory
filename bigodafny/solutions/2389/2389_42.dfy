// p04012 AtCoder Beginner Contest 044 - Beautiful Strings  (problem 2389, solution 2389_42)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// word = input()
// wset = set(word)
// a = 'Yes'
// for w in wset:
//   if word.count(w) % 2 != 0:
//     a = 'No'
// print(a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var freq: map<char, int> := map[];
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    var c := s[i];
    if c in freq {
      freq := freq[c := freq[c] + 1];
    } else {
      freq := freq[c := 1];
    }
    i := i + 1;
  }
  var a := "Yes";
  var j := 0;
  while j < |s|
    decreases |s| - j
  {
    if freq[s[j]] % 2 != 0 {
      a := "No";
    }
    j := j + 1;
  }
  output := a;
}
