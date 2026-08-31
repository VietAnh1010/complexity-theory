// 1131_B. Draw!  (problem 525, solution 525_273)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// pair = [None] * n
// 
// count = 0
// add = 0
// 
// for i in range(n):
//     pair[i] = list(map(int,input().split()))
// 
// 
// if(min(pair[0]) != 0):
//     add += min(pair[0]) + 1
// else:
//     add += 1
// 
// #print(add)
// 
// count+= add
// 
// for i in range(1,n):
//     if(min(pair[i])  - max(pair[i-1]) < 0):
//         continue
//     add = max( min(pair[i])  - max(pair[i-1]) + 1  , 0 )
//     if(pair[i-1][0] == pair[i-1][1]):
//         add -= 1
//     #print('bc',add)
//     count += add
// 
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, points: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
