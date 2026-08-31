// 1256_C. Platforms Jumping  (problem 1748, solution 1748_145)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n , m , d = map(int , input().split())
// array = list(map(int , input().split()))
// ss = sum(array)
// ans = [0] * (n + 1)
// s = 0
// for i in range(m) :
//     pos = min(s + d , n + 1 - ss)
//     for j in range(pos , pos + array[i]):
//         ans[j] = i + 1
//     s = pos + array[i] - 1
//     ss -= array[i]
// if s + d <= n :
//     print("NO")
// else :
//     print("YES")
//     for i in range(1 , n + 1) :
//         print(ans[i] , end=' ')
//     print("")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
