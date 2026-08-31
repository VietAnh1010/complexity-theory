// 746_B. Decoding  (problem 2830, solution 2830_421)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def solution(n,s):
// 	ans = [" "]*n
// 
// 	if n%2==0:
// 		p = int(n/2) - 1
// 		for i in range(n):
// 			if i%2==0:
// 				ans[p - int(i/2) ] = s[i]
// 			else:
// 				ans[p + int((i+1)/2) ] = s[i]
// 	else:
// 		p = int(n/2)
// 		for i in range(n):
// 			if i%2==0:
// 				ans[p + int(i/2) ] = s[i]
// 			else:
// 				ans[p - int((i+1)/2) ] = s[i]	
// 	return ''.join(ans)
// 
// n = int(input())
// s = input()
// print(solution(n,s))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
