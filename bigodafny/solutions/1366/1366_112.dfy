// 797_B. Odd sum  (problem 1366, solution 1366_112)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// n = int(input())
// a = list(map(int,input().split()))
// s=0
// mi = 100000000
// for i in a:
//     
//     if i>0:
//        s+=i
//     if i%2==1:
//         mi = min(mi,abs(i))
// 
// if s%2==0:
//     s -= mi
// print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
