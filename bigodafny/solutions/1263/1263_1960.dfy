// 1352_A. Sum of Round Numbers  (problem 1263, solution 1263_1960)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// import sys
// 
// ip = lambda : sys.stdin.readline()
// ipl = lambda : sys.stdin.readline().split()
// 
// for _ in range(int(ip())):
// 	n = int(input())
// 	res = []
// 	k = 1
// 	while n:
// 		if n % 10 != 0:
// 			res.append(n%10 * k)
// 		n //= 10
// 		k *= 10
// 	print(len(res))
// 	res.sort(reverse=True)
// 	print(*res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
