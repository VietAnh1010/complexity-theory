// p03687 AtCoder Grand Contest 016 - Shrinking  (problem 294, solution 294_131)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from sys import stdin
// s= (stdin.readline().rstrip())
// f = lambda a, b: abs(a-b-1)
// diff = lambda ls: map(f, ls[1:], ls)
// 
// ans = 100
// for i in set(s):
//     ans = min(ans,max([len(j) for j in s.split(i)]))
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var seen: set<char> := {};
  var ans := 100;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if s[i] !in seen {
      seen := seen + {s[i]};
      var v := MaxRunExcluding(s, s[i]);
      if v < ans { ans := v; }
    }
    i := i + 1;
  }
  output := IntToString(ans);
}

function MaxRunExcluding(s: string, c: char): int
{
  MaxRunHelper(s, c, 0, 0, 0)
}

function MaxRunHelper(s: string, c: char, idx: int, curRun: int, best: int): int
  requires 0 <= idx <= |s|
  decreases |s| - idx
{
  if idx == |s| then (if curRun > best then curRun else best)
  else if s[idx] == c then MaxRunHelper(s, c, idx + 1, 0, if curRun > best then curRun else best)
  else MaxRunHelper(s, c, idx + 1, curRun + 1, best)
}
