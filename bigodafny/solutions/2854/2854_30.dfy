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

ghost function U(adj: seq<seq<(int, int)>>, vis: seq<int>, k: nat): nat
  requires |vis| == |adj| && k <= |adj|
  decreases k
{ if k == 0 then 0 else U(adj, vis, k - 1) + (if vis[k - 1] == 0 then |adj[k - 1]| else 0) }

lemma UUpd(adj: seq<seq<(int, int)>>, vis: seq<int>, t: nat, k: nat)
  requires |vis| == |adj| && k <= |adj| && t < |adj|
  requires vis[t] == 0
  ensures U(adj, vis[t := 1], k) + (if t < k then |adj[t]| else 0) == U(adj, vis, k)
  decreases k
{
  if k > 0 { UUpd(adj, vis, t, k - 1); }
}

method Solve(n: int, edges: seq<string>) returns (output: string)
  requires n >= 0
  // same as 2854_107: a target is marked visited on pop, not on push.
{
  var adj: seq<seq<(int, int)>> := seq(n, _ => []);
  var idx := 0;
  while idx < |edges|
    invariant 0 <= idx <= |edges|
    invariant |adj| == n
    decreases |edges| - idx
  {
    var toks := SplitWs(edges[idx]);
    if |toks| >= 2 {
      var u := ParseInt(toks[0]) - 1;
      var v := ParseInt(toks[1]) - 1;
      if 0 <= u < |adj| && 0 <= v < |adj| {
        adj := adj[u := adj[u] + [(v, u)]];
        adj := adj[v := adj[v] + [(u, v)]];
      }
    }
    idx := idx + 1;
  }

  var visited: seq<int> := seq(n, _ => 0);
  var colors: seq<int> := seq(n, _ => 0);
  if n > 0 {
    visited := visited[0 := 1];
  }
  var options: seq<(int, int)> := if n > 0 && |adj| > 0 then adj[0] else [];
  while |options| > 0
    invariant |visited| == n
    invariant |colors| == n
    invariant |adj| == n
    decreases |options| + 2 * U(adj, visited, |adj|)
  {
    var t := options[|options| - 1];
    options := options[..|options| - 1];
    var tgt := t.0;
    var src := t.1;
    if 0 <= tgt < |visited| && visited[tgt] == 0 {
      UUpd(adj, visited, tgt, |adj|);
      visited := visited[tgt := 1];
      if 0 <= src < |colors| {
        colors := colors[tgt := 1 - colors[src]];
      }
      if 0 <= tgt < |adj| {
        options := options + adj[tgt];
      }
    }
  }

  var x := SumSeq(colors);
  output := IntToString(x * (n - x) - n + 1);
}
