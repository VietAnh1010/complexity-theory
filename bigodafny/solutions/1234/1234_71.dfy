// 1372_B. Omkar and Last Class of Math  (problem 1234, solution 1234_71)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// 
// def solve(n):
//     p = 1
//     for i in range(2, int(math.ceil(math.sqrt(n)))+1):
//         if n % i == 0:
//             p = i
//             break
//     if p != 1:
//         k = n//p
//     else:
//         k = 1
//     return " ".join([str(k), str(n - k)])
// 
// 
// def read():
//     t = int(input())
//     for i in range(t):
//         n = int(input())
//         ans = solve(n)
//         print(ans)
// 
// read()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
