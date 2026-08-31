// 546_C. Soldier and Cards  (problem 2680, solution 2680_65)
// time complexity: O(n**2+m**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import deque
// n = int(input())
// a = deque([int(i) for i in input().split()[1:]])
// b = deque([int(i) for i in input().split()[1:]])
// mark = set()
// ans = 0
// while a and b:
//     if str(a)+" "+str(b) in mark:
//         print(-1)
//         exit()
//     mark.add(str(a)+" "+str(b))
//     ans += 1
//     aa = a.popleft()
//     bb = b.popleft()
//     if aa > bb:
//         a.append(bb)
//         a.append(aa)
//     else:
//         b.append(aa)
//         b.append(bb)
// if a:
//     print(ans,1)
// else:
//     print(ans,2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, list1: seq<int>, list2: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
