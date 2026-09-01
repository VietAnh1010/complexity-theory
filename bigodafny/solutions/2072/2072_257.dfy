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

method Solve(s: string) returns (output: string)
{
  var n := |s|;
  var d := new char[4];
  var idx := 0;
  while idx < 4
    decreases 4 - idx
    modifies d
  {
    d[idx] := '?';
    idx := idx + 1;
  }
  idx := 0;
  while idx < n
    decreases n - idx
    modifies d
  {
    if s[idx] != '!' {
      d[idx % 4] := s[idx];
    }
    idx := idx + 1;
  }
  var countR := 0;
  var countB := 0;
  var countY := 0;
  var countG := 0;
  idx := 0;
  while idx < n
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
  }
  output := IntToString(countR) + " " + IntToString(countB) + " " + IntToString(countY) + " " + IntToString(countG);
}
