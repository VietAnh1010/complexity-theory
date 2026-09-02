// 112_A. Petya and Strings  (problem 3060, solution 3060_6262)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def sort(x, y):
//     a=sorted(x+y)
//     return a[-1]
// 
// n=input().lower()
// m=input().lower()
// 
// for i in range (0, len(n)):
//     if n[i]==m[i]:
//         if i==len(n)-1:
//             print(0)
//         continue
//     else:
//         if sort(n[i], m[i])==n[i]:
//             print(1)
//             break
//         else:
//             print(-1)
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string)
{
  var n: seq<char> := seq(|s1|, k requires 0 <= k < |s1| =>
    if s1[k] >= 'A' && s1[k] <= 'Z' then ((s1[k] as int) + 32) as char else s1[k]);
  var m: seq<char> := seq(|s2|, k requires 0 <= k < |s2| =>
    if s2[k] >= 'A' && s2[k] <= 'Z' then ((s2[k] as int) + 32) as char else s2[k]);
  var i := 0;
  while i < |n|
    invariant 0 <= i <= |n|
    decreases |n| - i
  {
    if i < |m| && n[i] == m[i] {
      if i == |n| - 1 {
        output := "0";
        return;
      }
      i := i + 1;
    } else if i < |m| {
      var mx := if n[i] > m[i] then n[i] else m[i];
      if mx == n[i] {
        output := "1";
      } else {
        output := "-1";
      }
      return;
    } else {
      output := "0";
      return;
    }
  }
  output := "0";
}
