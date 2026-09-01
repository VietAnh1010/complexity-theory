// 1165_A. Remainder  (problem 1622, solution 1622_48)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x,y = map(int,input().split())
// s = input()
// c=0
// for i in range(n-x,n):
//     if(i == n-y-1):
//         #print(1)
//         if(s[i]=='0'):
//             c = c + 1
//     else:
//         if(s[i]=='1'):
//             c=c+1
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, d: int, binary_list: seq<string>) returns (output: string)
{
  var c := 0;
  var i := n - k;
  while i < n
    decreases n - i
  {
    if i == n - d - 1 {
      if binary_list[i] == "0" {
        c := c + 1;
      }
    } else {
      if binary_list[i] == "1" {
        c := c + 1;
      }
    }
    i := i + 1;
  }
  output := IntToString(c);
}
