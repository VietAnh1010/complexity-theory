// 725_A. Jumping Ball  (problem 410, solution 410_176)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, s = int(input()), input()
// if '<' not in s or '>' not in s:
//     print(n)
// else:
//     print(s.find('>') + (n - 1 - s.rfind('<')))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, arrows: string) returns (output: string)
{
  var hasLt := ContainsChar(arrows, '<');
  var hasGt := ContainsChar(arrows, '>');
  if !hasLt || !hasGt {
    output := IntToString(n) + "\n";
  } else {
    var fi := FindFirst(arrows, '>');
    var la := FindLast(arrows, '<');
    output := IntToString(fi + (n - 1 - la)) + "\n";
  }
}

function ContainsChar(s: string, c: char): bool
  decreases |s|
{
  if |s| == 0 then false
  else if s[0] == c then true
  else ContainsChar(s[1..], c)
}

function FindFirst(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == c then 0
  else 1 + FindFirst(s[1..], c)
}

function FindLast(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then -1
  else
    var rest := FindLast(s[1..], c);
    if rest >= 0 then 1 + rest
    else if s[0] == c then 0
    else -1
}
