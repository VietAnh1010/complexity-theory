// 834_B. The Festive Evening  (problem 1830, solution 1830_0)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// n, k = map(int, input().split())
// a = list(input())
// st = [0] * 26
// ed = [0] * 26
// for i in range(n):
// 	if st[ord(a[i])-65] == 0:
// 		st[ord(a[i])-65] = i + 1
// 	else:
// 		ed[ord(a[i])-65] = i + 1
// for i in range(26):
// 	if st[i] != 0 and ed[i] == 0:
// 		ed[i] = st[i]
// n = 52
// i = 0
// j = 0
// maxi = -1 * sys.maxsize
// l = 0
// st.sort()
// ed.sort()
// while i < 26 and j < 26:
// 	if st[i] == 0:
// 		i += 1
// 		continue
// 	if ed[j] == 0:
// 		j += 1
// 		continue
// 	if st[i] <= ed[j]:
// 		l += 1
// 		i += 1
// 		if l > maxi:
// 			maxi = l
// 	else:
// 		l -= 1
// 		j += 1
// if maxi > k:
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, string_: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
