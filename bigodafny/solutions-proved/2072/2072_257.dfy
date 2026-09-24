// 758_B. Blown Garland  (problem 2072, solution 2072_257)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// d={}
// n=len(s)
// for i in range(n):
//     if(s[i]!='!'):
//         d[i%4]=s[i]
// l={'R':0,'B':0,'Y':0,'G':0}
// for i in range(n):
//     if(s[i]=='!'):
//         l[d[i%4]]+=1
// print(*list(l.values()))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 12 * |s| + 30
{
  steps := 1;
  var n := |s|;
  var d := seq(4, _ => ' ');
  var idx := 0;
  while idx < 4
    invariant 0 <= idx <= 4
    invariant |d| == 4
    invariant steps <= 1 + 2 * idx
    decreases 4 - idx
  {
    d := d[idx := '?'];
    idx := idx + 1;
    steps := steps + 2;
  }
  idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant |d| == 4
    invariant steps <= 9 + 4 * idx
    decreases n - idx
  {
    if s[idx] != '!' {
      d := d[idx % 4 := s[idx]];
    }
    idx := idx + 1;
    steps := steps + 4;
  }
  var countR := 0;
  var countB := 0;
  var countY := 0;
  var countG := 0;
  idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant |d| == 4
    invariant steps <= 9 + 4 * n + 4 * idx
    decreases n - idx
  {
    if s[idx] == '!' {
      var c := d[idx % 4];
      if c == 'R' {
        countR := countR + 1;
      } else if c == 'B' {
        countB := countB + 1;
      } else if c == 'Y' {
        countY := countY + 1;
      } else if c == 'G' {
        countG := countG + 1;
      }
    }
    idx := idx + 1;
    steps := steps + 4;
  }
  output := IntToString(countR) + " " + IntToString(countB) + " " + IntToString(countY) + " " + IntToString(countG);
  steps := steps + 8;
}
