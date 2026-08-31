// 729_A. Interview with Oleg  (problem 307, solution 307_14)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// for i in range(100, 0, -1):
//     s = s.replace('o' + 'go' * i, '***')
// print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  var cur := s;
  var i := 100;
  while i >= 1
    decreases i
  {
    var pat := "o" + RepeatGo(i);
    cur := ReplaceAll(cur, pat, "***");
    i := i - 1;
  }
  output := cur + "\n";
}

function RepeatGo(i: int): string
  requires i >= 0
  decreases i
{
  if i == 0 then "" else "go" + RepeatGo(i - 1)
}

method ReplaceAll(s: string, pat: string, rep: string) returns (res: string)
  requires |pat| > 0
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if i + |pat| <= |s| && s[i..i+|pat|] == pat {
      parts := parts + [rep];
      i := i + |pat|;
    } else {
      parts := parts + [[s[i]]];
      i := i + 1;
    }
  }
  res := Join(parts, "");
}
