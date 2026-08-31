// 901_A. Hashing Trees  (problem 2723, solution 2723_42)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def read():
// 	return tuple(int(x) for x in input().split())
// 
// def main():
// 	(h, ) = read()
// 	a = read()
// 	tree = []
// 	fi = 0
// 	flag = False
// 	for i, x in enumerate(a):
// 		if fi == 0:
// 			if not flag and x > 1:
// 				flag = True
// 			elif flag and x > 1:
// 				fi = len(tree)
// 			else:
// 				flag = False
// 		tree.extend([len(tree)] * x)
// 	if fi == 0:
// 		print('perfect')
// 		return
// 	else:
// 		print('ambiguous')
// 	print(' '.join(str(x) for x in tree))
// 	tree[fi] = fi - 1
// 	print(' '.join(str(x) for x in tree))
// 
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
