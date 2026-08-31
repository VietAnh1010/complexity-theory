// 1208_B. Uniqueness  (problem 2650, solution 2650_140)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// data = list(map(int, input().split(' ')))
// seq = sorted(data)
// seq2 = []
// for i in range(0, len(seq)):
//     if (i == 0) or (seq[i-1] != seq[i]):
//         seq2.append(seq[i])
// for i in range(0, len(data)):
//     l = 0
//     r = len(seq2)
//     while r-l > 1:
//         mid = (r+l)//2
//         if (seq2[mid] < data[i]):
//             l = mid + 1
//         elif (seq2[mid] == data[i]):
//             l = mid
//         else:
//             r = mid
//     data[i] = l
// ans = int(1e9)
// pref = 0
// used = list()
// for x in range(n):
//     used.append(0)
// while pref <= n:
//     if pref > 0:
//         if used[data[pref-1]] > 0:
//             break
//         used[data[pref-1]] += 1
//     dused = used.copy()
//     suf = 0
//     while suf < n:
//         ind = data[n - 1 - suf]
//         if dused[ind] > 0:
//             break
//         dused[ind] += 1
//         suf += 1
//     ans = min(ans, n - pref - suf)
//     pref += 1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
