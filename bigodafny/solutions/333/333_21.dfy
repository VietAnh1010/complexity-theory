// 938_A. Word Correction  (problem 333, solution 333_21)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// k = input()
// s = input()
// vowels = ['a','e','i','o','u','y']
// new = []
// new.append(s[0])
// curr = s[0]
// for i in range(1, len(s)):
//     if curr in vowels and s[i] in vowels:
//         continue
//     else:
//         new.append(s[i])
//         curr = s[i]
// 
// print(''.join(new))
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
    decreases |word| - i
  {
    if IsVowelWC21(curr) && IsVowelWC21(word[i]) {
      // skip: continue in original
    } else {
      buf[j] := word[i];
      j := j + 1;
      curr := word[i];
    }
    i := i + 1;
  }
  output := buf[0..j] + "\n";
}

predicate IsVowelWC21(c: char)
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y'
}
