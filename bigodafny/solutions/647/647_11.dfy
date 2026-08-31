// 859_C. Pie Rules  (problem 647, solution 647_11)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// X = list(map(int, input().split()))
// 
// ali = [None]*(n+1)
// bob = [None]*(n+1)
// 
// ali[n] = 0
// bob[n] = 0
// 
// for i in range(n-1, -1, -1):
// 	bob[i] = max(bob[i+1], ali[i+1]+X[i])
// 	ali[i] = sum(X[i:n]) - bob[i]
// 	
// #print(ali)
// #print(bob)
// 
// print(ali[0], bob[0], sep=' ')
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
