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
