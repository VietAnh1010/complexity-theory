// 53_A. Autocomplete  (problem 1196, solution 1196_100)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// target = input()
// count = input()
// srchlist = []
// for i in range(0,int(count)):
//     srch = input()
//     srchlist.append(srch)
// srchlist.sort()
// final = target
// for item in srchlist:
//     if item.find(target) == 0:
//         final = item
//         break
// print(final)
// 	 			 					  	 	    		 		  		
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(text: string, n: int, text_list: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
