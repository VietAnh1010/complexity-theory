// 208_D. Prizes, Prizes, more Prizes  (problem 1092, solution 1092_11)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// sum,a,b,c,d,e=0,0,0,0,0,0
// numbers = [int(x) for x in input().split(' ')]
// prizes = [int(x) for x in input().split(' ')]
// prizes.sort()
// 
// for num in numbers:
//     sum+=num
//     if sum >= prizes[4]:
//         e+=int(sum/prizes[4])
//         sum = sum%prizes[4]
//     if sum >= prizes[3]:
//         d+=int(sum/prizes[3])
//         sum = sum%prizes[3]
//     if sum >= prizes[2]:
//         c+=int(sum/prizes[2])
//         sum = sum%prizes[2]
//     if sum >= prizes[1]:
//         b+=int(sum/prizes[1])
//         sum = sum%prizes[1]
//     if sum >= prizes[0]:
//         a+=int(sum/prizes[0])
//         sum = sum%prizes[0]
// print(f'{a} {b} {c} {d} {e}')
// print(sum)
//   		 	    		 	 	  	   					 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
