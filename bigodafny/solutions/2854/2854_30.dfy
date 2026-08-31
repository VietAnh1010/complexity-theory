// 862_B. Mahmoud and Ehab and the bipartiteness  (problem 2854, solution 2854_30)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// G = []
// for i in range(n):
//     G.append([])
// for i in range(n-1):
//     u,v = [int(x)-1 for x in input().split()]
//     G[u].append((v,u))
//     G[v].append((u,v))
// 
// options = G[0]
// visited = [0]*n
// visited[0] = 1
// colors = [0]*n
// while options:
//     t = options.pop()
//     if visited[t[0]] == 0:
//         visited[t[0]] = 1
//         colors[t[0]] = 1-colors[t[1]]
//         options.extend(G[t[0]])
// 
// x = sum(colors)
// print(x*(n-x)-n+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
