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

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 6 * |s| + 6
{
  var freq: map<char, int> := map[];
  var i := 0;
  steps := 1;
  ghost var base1 := steps;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall t :: 0 <= t < i ==> s[t] in freq
    invariant steps <= base1 + 3 * i
    decreases |s| - i
  {
    var c := s[i];
    if c in freq {
      freq := freq[c := freq[c] + 1];
    } else {
      freq := freq[c := 1];
    }
    i := i + 1;
    steps := steps + 3;
  }
  var a := "Yes";
  var j := 0;
  ghost var base2 := steps;
  while j < |s|
    invariant 0 <= j <= |s|
    invariant forall t :: 0 <= t < |s| ==> s[t] in freq
    invariant steps <= base2 + 3 * j
    decreases |s| - j
  {
    if freq[s[j]] % 2 != 0 {
      a := "No";
    }
    j := j + 1;
    steps := steps + 3;
  }
  output := a;
  steps := steps + 2;
}
