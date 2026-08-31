// 1547_B. Alphabetical Strings  (problem 2087, solution 2087_50)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for _ in range(int(input())):
//     a=input()
//     s=""
//     while  len(a)!=1:
//         if a[0]>a[-1]:
//             s+=a[0]
//             a=a[1:]
//         else:
//             s+=a[-1]
//             a=a[:-1]
// 
//         if len(a)==1:
//             break
//     s+="a"
//     if a!="a" or s[::-1] not in "abcdefghijklmnopqrstuvwxyz":
//         print("NO")
//     else:
//         print("YES")
//             
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(strings: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
