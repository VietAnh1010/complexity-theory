// p04012 AtCoder Beginner Contest 044 - Beautiful Strings  (problem 2389, solution 2389_139)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// ch=0
// for i in s:
//   if s.count(i)%2 ==1:
//     ch=1
// print("YNeos"[ch::2])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

method Solve(s: string) returns (output: string)
{
  var ch := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if CountChar(s, s[i]) % 2 == 1 {
      ch := 1;
    }
    i := i + 1;
  }
  output := if ch == 0 then "Yes" else "No";
}
