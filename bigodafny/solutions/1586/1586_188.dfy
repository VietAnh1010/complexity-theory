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
  var macas := Sort(scores, (x: int, y: int) => x > y);
  var amigo1 := 0;
  var amigo2 := 0;
  var i := 0;
  while i < |macas|
    decreases |macas| - i
  {
    if amigo1 <= amigo2 {
      amigo1 := amigo1 + macas[i];
    } else {
      amigo2 := amigo2 + macas[i];
    }
    i := i + 1;
  }
  if amigo1 == amigo2 {
    output := "YES";
  } else {
    output := "NO";
  }
}
