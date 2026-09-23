// 981_A. Antipalindrome  (problem 2269, solution 2269_59)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
//
// s = input()
//
// def isPalindrome(s):
//     l = len(s)
//     for i in range(l // 2):
//         if s[i] != s[l - i - 1]:
//             return False
//     return True
//
// if not isPalindrome(s):
//     print(len(s))
// elif all([c == s[0] for c in s]):
//     print(0)
// else:
//     print(len(s) - 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 3 * |s| + |output| + 6
{
  IsPalindromeFromCost(s, 0, |s| / 2);
  if !IsPalindrome269b(s) {
    output := IntToString(|s|);
    steps := (|s| / 2) + |output| + 3;
  } else {
    AllSameFromCost(s, 0);
    if AllSameChar269b(s) {
      output := IntToString(0);
      steps := (|s| / 2) + |s| + |output| + 4;
    } else {
      output := IntToString(|s| - 1);
      steps := (|s| / 2) + |s| + |output| + 4;
    }
  }
}

function IsPalindrome269b(s: string): bool
{
  IsPalindromeFrom269b(s, 0, |s| / 2)
}

function IsPalindromeFrom269b(s: string, i: int, half: int): bool
  requires 0 <= i
  requires half <= |s|
  decreases half - i
{
  if i >= half then true
  else if s[i] != s[|s| - i - 1] then false
  else IsPalindromeFrom269b(s, i + 1, half)
}

// The recursion does one unit of work per step from i up to half; its call
// count is therefore bounded by half - i.
lemma IsPalindromeFromCost(s: string, i: int, half: int)
  requires 0 <= i
  requires half <= |s|
  decreases half - i
{
  if i >= half {
  } else if s[i] != s[|s| - i - 1] {
  } else {
    IsPalindromeFromCost(s, i + 1, half);
  }
}

function AllSameChar269b(s: string): bool
  requires |s| >= 0
{
  AllSameFrom269b(s, 0)
}

function AllSameFrom269b(s: string, i: int): bool
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| || |s| == 0 then true
  else if s[i] != s[0] then false
  else AllSameFrom269b(s, i + 1)
}

lemma AllSameFromCost(s: string, i: int)
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| || |s| == 0 {
  } else if s[i] != s[0] {
  } else {
    AllSameFromCost(s, i + 1);
  }
}
