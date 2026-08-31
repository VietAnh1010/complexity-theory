// 1199_A. City Day  (problem 1820, solution 1820_180)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n , x , y = map(int,input().split())
// arr = list(map(int,input().split()))
// 
// for i in range(n):
//     if i >= x :
//         if arr[i] == min(arr[i - x : i + y + 1]):
//             print(i + 1 )
//             break
//     else:
//         if arr[i] == min(arr[0 : i + y +1]):
//             print(i + 1 )
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
