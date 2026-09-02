// 560_A. Currency System in Geraldion  (problem 1437, solution 1437_223)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def meuIn(num, valores):
//     for i in valores:
//         if(i == num):
//             return True
//         if(i > num):
//             return False
//     return False
// 
// def verificaValores(valores):
// 
//     if(not meuIn(1, valores)):
//         return 1
// 
//     return -1
// 
// num = int(input())
// entrada = input().split()
// 
// valores = [int(valor) for valor in entrada]
// valores.sort()
// 
// print(verificaValores(valores))
// 	 	 		  	  			 	  	 	 		 	  	 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string, a_list: seq<int>) returns (output: string)
{
  output := IntToString(if 1 in a_list then -1 else 1);
}
