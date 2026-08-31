// 1011_B. Planning The Expedition  (problem 1306, solution 1306_15)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// num_part, num_pack = [int(i) for i in input().split(' ')]
// type_pack = input().split(' ')
// dict_count = {}
// for element in set(type_pack):
//     dict_count[element] = type_pack.count(element)
// count = 0
// for days in range(1,101):
// 	survival = 0
// 	for element in dict_count:
// 		survival += dict_count[element] // days
// 	if survival >= num_part:
// 		count += 1
// 	else:
// 		break
// 
// 
// print(count)
//   	 	    		  		 				 		  	  	 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
