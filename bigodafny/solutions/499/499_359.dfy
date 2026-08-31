// 1206_B. Make Product Equal One  (problem 499, solution 499_359)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = input() #the number of numbers
// a = list(map(int, input().split())) #the numbers
// 
// answer = 0 #initial value of answer
// cnt_minus = 0 #the number of (-)
// cnt_0 = 0 #the number of 0
// for i in a:
//     if i<0:
//         answer +=abs(i+1)
//         cnt_minus += 1
//     if i==0:
//         answer += 1
//         cnt_0 += 1
//     if i>0:
//         answer +=abs(i-1)
// 
// if cnt_0 == 0:
//     if cnt_minus%2 == 0:
//         print(answer)
//     else:
//         print(answer+2)
// else:
//     print(answer)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
