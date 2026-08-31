// 489_B. BerSU Ball  (problem 1718, solution 1718_621)
// time complexity: O(nlogn+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(x) for x in input().split()]
// m = int(input())
// b = [int(x) for x in input().split()]
// 
// a = sorted(a)
// b = sorted(b)
// 
// idx_a = 0
// idx_b = 0
// cnt = 0
// while(idx_a < n and idx_b < m):
// 
// 	if( abs(a[idx_a]-b[idx_b]) <= 1):
// 		idx_a+=1
// 		idx_b+=1
// 		cnt+=1
// 
// 	elif(a[idx_a]>b[idx_b]):
// 		idx_b+=1
// 	else:
// 		idx_a+=1
// 
// print(cnt)
// #FernandezFernandez2019
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N1: int, list1: seq<int>, N2: int, list2: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
