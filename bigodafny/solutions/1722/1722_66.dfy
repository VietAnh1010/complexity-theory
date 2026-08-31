// 887_B. Cubes for Masha  (problem 1722, solution 1722_66)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = []
// a += [list(input())]
// if (n > 1):
//     a += [list(input())]
// if (n > 2):
//     a += [list(input())]
// i = 1
// while (i < 1000):
//     s = list(str(i))
//     if (n == 1):
//         if (s[0] in a[0]):
//             i += 1
//             continue
//     if (n == 2):
//         if (len(s) == 1 and (s[0] in a[0] or s[0] in a[1])):
//             i += 1
//             continue
//         if (len(s) == 2 and (
//             (s[0] in a[0] and s[1] in a[1]) or
//             (s[0] in a[1] and s[1] in a[0]))):
//             i += 1
//             continue
//     if (n == 3):
//         if (len(s) == 1 and (s[0] in a[0] or s[0] in a[1] or s[0] in a[2])):
//             i += 1
//             continue
//         if (len(s) == 2 and (
//             (s[0] in a[0] and s[1] in a[1]) or
//             (s[0] in a[0] and s[1] in a[2]) or
//             (s[0] in a[1] and s[1] in a[0]) or
//             (s[0] in a[1] and s[1] in a[2]) or
//             (s[0] in a[2] and s[1] in a[0]) or
//             (s[0] in a[2] and s[1] in a[1]))):
//             i += 1
//             continue
//         if (len(s) == 3 and (
//             (s[0] in a[0] and s[1] in a[1] and s[2] in a[2]) or
//             (s[0] in a[0] and s[1] in a[2] and s[2] in a[1]) or
//             (s[0] in a[1] and s[1] in a[0] and s[2] in a[2]) or
//             (s[0] in a[1] and s[1] in a[2] and s[2] in a[0]) or
//             (s[0] in a[2] and s[1] in a[0] and s[2] in a[1]) or
//             (s[0] in a[2] and s[1] in a[1] and s[2] in a[0])
//             )):
//             i += 1
//             continue
//     print (i-1)
//     break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
