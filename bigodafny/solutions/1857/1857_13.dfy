// 903_C. Boxes Packing  (problem 1857, solution 1857_13)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #!/user/bin/env/python 3.5
// #---*--- code: utf-8 ---*---
// 
// n=int(input())
// a=input().split(' ')
// num=0
// for i in a:
// 	num=max(num,a.count(i))
// 
// print(num)
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
