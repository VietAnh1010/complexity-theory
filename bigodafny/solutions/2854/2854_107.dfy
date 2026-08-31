// 862_B. Mahmoud and Ehab and the bipartiteness  (problem 2854, solution 2854_107)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def readln(): return map(int, input().rstrip().split())
// 
// 
// data = {}
// n = int(input())
// for i in range(1, n + 1):
//     data[i] = []
// for i in range(0, n - 1):
//     u, v = readln()
//     data[u].append(v)
//     data[v].append(u)
// 
// l = [0, 0]
// visited = [False] * (n + 1)
// 
// stk = [(1, 0)]
// while stk:
//     u = stk.pop()
//     visited[u[0]] = True
//     l[u[1]] += 1
//     for i in data[u[0]]:
//         if not visited[i]:
//             stk.append((i, 1 - u[1]))
// 
// print(l[0] * l[1] - (n - 1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
