// 486_C. Palindrome Transformation  (problem 1387, solution 1387_19)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, p = map(int, input().split())
// p -= 1
// s = input()
// ans = 0
// idx = 0
// pos = []
// while idx < n//2:
//     if s[idx] != s[n-1-idx]:
//         diff = abs(ord(s[idx]) - ord(s[n-1-idx]))
//         ans += min(diff, 26 - diff)
//         if p >= n//2:
//             pos.append(n-1-idx)
//         else:
//             pos.append(idx)
//     idx += 1
// pos.sort()
// #print(ans)
// 
// if ans == 0:
//     print(0)
// elif len(pos) == 1:
//     ans += abs(p - pos[0])
//     print(ans)
// else:
//     if abs(p - pos[0]) < abs(p - pos[-1]):
//         ans += abs(p - pos[0]) + (pos[-1] - pos[0])
//     else:
//         ans += abs(p - pos[-1]) + (pos[-1] - pos[0])
// 
//     print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function MinInt1387a(a: int, b: int): int { if a < b then a else b }

method Solve(n: int, k: int, s: string) returns (output: string)
{
  var p := k - 1;
  var ans := 0;
  var pos: seq<int> := [];
  var idx := 0;
  var half := n / 2;
  while idx < half
    decreases half - idx
  {
    if s[idx] != s[n-1-idx] {
      var diff := AbsInt((s[idx] as int) - (s[n-1-idx] as int));
      ans := ans + MinInt1387a(diff, 26 - diff);
      if p >= half {
        pos := pos + [n-1-idx];
      } else {
        pos := pos + [idx];
      }
    }
    idx := idx + 1;
  }
  var sortedPos := SortInts(pos);
  if ans == 0 {
    output := "0";
  } else if |sortedPos| == 1 {
    output := IntToString(ans + AbsInt(p - sortedPos[0]));
  } else {
    var first := sortedPos[0];
    var last := sortedPos[|sortedPos|-1];
    var a1 := AbsInt(p - first);
    var a2 := AbsInt(p - last);
    if a1 < a2 {
      output := IntToString(ans + a1 + (last - first));
    } else {
      output := IntToString(ans + a2 + (last - first));
    }
  }
}
