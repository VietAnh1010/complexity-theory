// 486_C. Palindrome Transformation  (problem 1387, solution 1387_34)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,p = map(int,input().split())
// s = input()
// p = n-p if p > n//2 else p-1
// left,right,steps = n//2,-1,0
// for i in range(n//2):
//     x = abs(ord(s[i]) - ord(s[-i-1]))
//     steps += min(x,26-x)
//     if (x!=0) :
//         left = min(left,i)
//         right = max(right,i)
// if (steps) :
//     print (steps + right-left + min(abs(p-left),abs(right-p)))
// else:
//     print(0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
