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
  var adj: seq<seq<int>> := seq(n + 1, _ => []);
  var idx := 0;
  while idx < |edges|
    invariant 0 <= idx <= |edges|
    invariant |adj| == n + 1
    decreases |edges| - idx
  {
    var toks := SplitWs(edges[idx]);
    if |toks| >= 2 {
      var u := ParseInt(toks[0]);
      var v := ParseInt(toks[1]);
      if 0 <= u < |adj| && 0 <= v < |adj| {
        adj := adj[u := adj[u] + [v]];
        adj := adj[v := adj[v] + [u]];
      }
    }
    idx := idx + 1;
  }

  var visited: seq<bool> := seq(n + 1, _ => false);
  var l0 := 0;
  var l1 := 0;
  var stack: seq<(int, int)> := [(1, 0)];
  while |stack| > 0
    invariant |visited| == n + 1
    invariant |adj| == n + 1
  {
    var top := stack[|stack| - 1];
    stack := stack[..|stack| - 1];
    var node := top.0;
    var color := top.1;
    if 0 <= node < |visited| {
      visited := visited[node := true];
    }
    if color == 0 { l0 := l0 + 1; } else { l1 := l1 + 1; }
    if 0 <= node < |adj| {
      var nbrs := adj[node];
      var k := 0;
      while k < |nbrs|
        invariant 0 <= k <= |nbrs|
        decreases |nbrs| - k
      {
        var nb := nbrs[k];
        if 0 <= nb < |visited| && !visited[nb] {
          stack := stack + [(nb, 1 - color)];
        }
        k := k + 1;
      }
    }
  }

  output := IntToString(l0 * l1 - (n - 1));
}
