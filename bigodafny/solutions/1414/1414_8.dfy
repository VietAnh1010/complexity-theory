// 1494_A. ABC String  (problem 1414, solution 1414_8)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def solve(n, a):
//     cnt = {"A": 0, "B": 0, "C": 0}
//     for i in range(n):
//         cnt[a[i]] += 1
//     vs = sorted(cnt.values())
//     if vs[0] + vs[1] != vs[2]:
//         return False
//     first = a[0]
//     last = a[-1]
//     if first == last:
//         return False
//     other = first
//     if cnt[first] == vs[2]:
//         other = last
//     num_open = 0
//     for i in range(n):
//         if a[i] == first:
//             num_open += 1
//         elif a[i] == last:
//             num_open -= 1
//         elif other == first:
//             num_open += 1
//         else:
//             num_open -= 1
//         if num_open < 0:
//             return False
//     return num_open == 0
// 
// def main():
//     t = int(input())
//     for _ in range(t):
//         a = input(); n = len(a)
//         if solve(n, a):
//             print("YES")
//         else:
//             print("NO")
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
