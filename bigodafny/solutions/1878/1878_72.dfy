// 416_A. Guess a number!  (problem 1878, solution 1878_72)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// l = []
// less = []
// grt = []
// 
// for i in range(n):
//     l = [x for x in input().split()]
// 
//     if l[2] == 'N':
//         l[2] = 'Y'
//         if l[0] == '>=': l[0] = '<'
//         elif l[0] == '>': l[0] = '<='
//         elif l[0] == '<': l[0] = '>='
//         else: l[0] = '>'
//     
//     if (l[0] == "<" or l[0] == "<="):
//         less.append(int(l[1]))
//         if l[0] == "<":
//             less[-1] -= 1
// 
//     elif (l[0] == ">" or l[0] == ">="):
//         grt.append(int(l[1]))
//         if l[0] == ">":
//             grt[-1] += 1
//             
// ##    print(less, grt)
// 
// less.sort()
// grt.sort()
// 
// if len(less) > 0 and len(grt) > 0:
//     v1 = less[0]
//     v2 = grt[-1]
// 
//     if v1 >= v2:
//         print(v2)
//     else:
//         print("Impossible")
// elif len(less) == 0 and len(grt) > 0:
//     print(grt[-1])
// elif len(grt) == 0 and len(less) > 0:
//     print(less[0])
// elif len(less) == 0 and len(grt) == 0:
//     print("Impossible")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, queries: seq<(string, int, string)>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
