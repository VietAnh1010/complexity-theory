// 1011_B. Planning The Expedition  (problem 1306, solution 1306_197)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// 
// n,m = list(map(int,input().split()))
// l = list(map(int,input().split()))
// 
// l2 = [y for x,y in Counter(l).items()]
// l2.sort(reverse=True)
// 
// #print(l2)
// 
// for i in range(1,max(l2)+2):
// 	if sum(int(x/i) for x in l2) < n:
// 		print(i-1)
// 		break
// else:
// 	print()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
