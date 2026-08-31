// 433_A. Kitahara Haruki's Gift  (problem 1586, solution 1586_188)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// macas = list(map(int, input().split(" ")))
// macas.sort(reverse=True)
// 
// amigo_1 = 0
// amigo_2 = 0
// 
// for maca in macas:
//     if amigo_1 <= amigo_2:
//         amigo_1 += maca
//     else:
//         amigo_2 += maca
// 
// if amigo_1 == amigo_2:
//     print("YES")
// else:
//     print("NO")
// 							    		  	 	     		 				
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, scores: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
