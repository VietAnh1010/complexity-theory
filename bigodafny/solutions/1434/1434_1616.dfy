// 228_A. Is your horseshoe on the other hoof?  (problem 1434, solution 1434_1616)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = list(map(int,input().split()))
// count = 0
// 
// for i in range(1,len(a)):
// 	if a[i] in a[:i]:
// 		count += 1
// print(count)	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(values: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
