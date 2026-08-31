// 938_A. Word Correction  (problem 333, solution 333_197)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #/usr/bin/python3
// 
// # MC721A
// # 27 de março de 2020
// # Rogério Meirelles - RA160245
// 
// n = int(input())
// word = [char for char in input()]
// vowels = ['a', 'e', 'i', 'o', 'u', 'y']
// remove = []
// 
// for i in range(1, n):
//     if word[i] in vowels and word[i-1] in vowels:
//         remove.append(i)
// 
// remove.sort(reverse=True)
// 
// for r in remove:
//     word.pop(r)
// 
// print(''.join(word))
// 	 	 	 	 	   	 	 	    	     			
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, word: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
