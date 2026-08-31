// 977_F. Consecutive Subsequence  (problem 952, solution 952_163)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [*map(int, input().split())]
// c = [None] * n
// whereIs = [None] * n
// for i in range(0, n):
//     c[i] = i
// c.sort(key=lambda value:a[value])
// tot = 0
// for i in range(0, n):
//     if i == 0 or a[c[i]] != a[c[i - 1]]:
//         whereIs[c[i]] = tot
//         tot += 1
//     else :
//         whereIs[c[i]] = whereIs[c[i - 1]]
// dp = [0] * n
// preState = [None] * n
// lst = [-1] * n
// res = 0
// ptr = -1
// for i in range(0, n):
//     if whereIs[i] == 0:
//         preState[i] = -1
//         dp[i] = 1
//     else:
//         preState[i] = lst[whereIs[i] - 1]
//         if a[preState[i]] != a[i] - 1:
//             preState[i] = -1;
// 
//         # print("tset : ", preState[i], end="\n")
//         if preState[i] != -1:
//             dp[i] = dp[preState[i]] + 1
//         else:
//             dp[i] = 1
// 
//     lst[whereIs[i]] = i
//     # print(i, " : ", dp[i], " where : ", whereIs[i], end="! \n")
// 
//     res = max(res, dp[i])
//     if res == dp[i]:
//         ptr = i
// print(res)
// resArr = [-1] * res
// while res > 0:
//     resArr[res - 1] = ptr + 1
//     ptr = preState[ptr]
//     res -= 1
// print(' '.join(map(str, resArr)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
