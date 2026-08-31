// 59_B. Fortune Telling  (problem 384, solution 384_38)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// input_list = list(map(int,input().split()))
// input_list.sort()
// x = sum(input_list)
// if(x%2 ==1):
//     print(x)
// else:
//     for i in range(n):
//         if(input_list[i]%2 == 1):
//             print(x-input_list[i])
//             break
//     else:
//         print(0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
