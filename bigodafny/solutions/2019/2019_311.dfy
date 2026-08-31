// 839_A. Arya and Bran  (problem 2019, solution 2019_311)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// a = list(map(int, input().split()))
// count = tank = 0
// for i in range(n):
// 	tank+=a[i]
// 	if tank>=8:
// 		count+=1
// 		tank-=8
// 		k-=8
// 	else:
// 		count+=1
// 		k-=tank
// 		tank=0
// 	if k<=0:
// 		break
// if k>0:
// 	print(-1)
// else:
// 	print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
