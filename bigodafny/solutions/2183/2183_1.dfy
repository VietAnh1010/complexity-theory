// p02293 Parallel/Orthogonal  (problem 2183, solution 2183_1)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// EPS = 1e-4
// 
// #外積
// def OuterProduct(one, two):
// 	tmp = one.conjugate() * two
// 	return tmp.imag
// 
// #内積
// def InnerProduct(one, two):
// 	tmp = one.conjugate() * two
// 	return tmp.real
// 
// def solve(a, b, c, d):
// 	if abs(OuterProduct(b-a, d-c)) <= EPS:
// 		return 2
// 	elif abs(InnerProduct(b-a, d-c)) <= EPS:
// 		return 1
// 	else:
// 		return 0
// 
// n = int(input())
// for _ in range(n):
// 	pp = list(map(int, input().split()))
// 	p = [complex(pp[i], pp[i+1]) for i in range(0, 8, 2)]
// 	print(solve(p[0], p[1], p[2], p[3]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rows: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
