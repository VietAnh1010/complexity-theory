// 186_A. Comparing Strings  (problem 1243, solution 1243_178)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # http://codeforces.com/problemset/problem/186/A
// a = list(input())
// b = list(input())
// ans = 'NO'
// 
// if len(a)==len(b):
//     l = []
//     for i in range(len(a)):
//         if a[i]!= b[i]:
//             l.append(i)
//     if len(l) == 2:
//         a[l[0]],a[l[1]] = a[l[1]], a[l[0]]
//         if a == b:
//             ans = 'YES'
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
