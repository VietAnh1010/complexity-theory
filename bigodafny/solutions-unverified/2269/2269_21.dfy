// 981_A. Antipalindrome  (problem 2269, solution 2269_21)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s, r = input(), 0
// i = len(s)
// while i > r:
//     for j in range(i - r):
//         t = s[j:i]
//         if t != t[::-1]:
//             r = i - j
//             break
//     i -= 1
// print(r)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var r := 0;
  var i := |s|;
  while i > r
    decreases i
  {
    var j := 0;
    var found := false;
    while j < i - r && !found
      decreases (i - r) - j
    {
      var t := s[j..i];
      if !IsPalindrome269(t) {
        r := i - j;
        found := true;
      }
      j := j + 1;
    }
    i := i - 1;
  }
  output := IntToString(r);
}

function IsPalindrome269(t: string): bool
{
  IsPalindromeFrom269(t, 0, |t| - 1)
}

function IsPalindromeFrom269(t: string, lo: int, hi: int): bool
  decreases hi - lo
{
  if lo >= hi then true
  else if t[lo] != t[hi] then false
  else IsPalindromeFrom269(t, lo + 1, hi - 1)
}
