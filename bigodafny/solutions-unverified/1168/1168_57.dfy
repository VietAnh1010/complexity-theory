// 1322_A. Unusual Competitions  (problem 1168, solution 1168_57)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def fn():
//     diff = 0
//     ans = 0
//     f = 'p'
//     n = int(input())
//     s = input()
//     if len(s) % 2 == 1:
//         return -1
// 
//     for i in range(n):
//         if s[i] == '(': diff += 1
//         elif s[i] == ')': diff -= 1
// 
//         if diff >= 0:
//             f = 'p'
//             continue
// 
//         elif diff < 0:
//             ans += 1
//             if f == 'p':
//                 f = 'n'
//                 ans +=1
//     if diff == 0:
//         return ans
//     else:
//         return -1
// 
// print(fn())
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  if |s| % 2 == 1 {
    output := "-1";
  } else {
    var diff := 0;
    var ans := 0;
    var f := 'p';
    var i := 0;
    while i < n
      decreases n - i
    {
      if s[i] == '(' {
        diff := diff + 1;
      } else if s[i] == ')' {
        diff := diff - 1;
      }
      if diff >= 0 {
        f := 'p';
      } else {
        ans := ans + 1;
        if f == 'p' {
          f := 'n';
          ans := ans + 1;
        }
      }
      i := i + 1;
    }
    if diff == 0 {
      output := IntToString(ans);
    } else {
      output := "-1";
    }
  }
}
