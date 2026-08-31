// 389_A. Fox and Number Game  (problem 281, solution 281_12)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = eval(input())
// no = list(map(eval,input().split()))
// while True:
//     flag = False
//     for i in no:
//         if i<=0:
//             continue
//         for j in range(n):
//             if no[j]>i:
//                 flag = True
//                 if no[j]%i == 0:
//                     no[j] = i
//                 else:
//                     no[j] = no[j]%i
//     if flag == False:
//         break
// # print(no)
// sum = 0
// for i in no:
//     sum += i
// print(int(sum))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
