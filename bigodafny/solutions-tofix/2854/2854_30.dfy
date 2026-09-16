// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-22
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     adj := adj[u := adj[u] + [(v,u)]] and adj := adj[v := ...] are seq
//     updates over the n-length adj sequence executed inside the |edges|
//     loop, each O(n), giving O(n**2) for adjacency alone; the Python
//     instead uses G[u].append((v,u)), an O(1) list append, matching its
//     own O(n) label.
//
//   how this label could be wrong, and what to check:
//     The label assumes adjacency-list construction is O(1) per append as
//     in Python's G[u].append. Open the edge loop and check that adj :=
//     adj[u := adj[u] + [(v,u)]] is a top-level update of the whole
//     n-length adj sequence, repeated twice per edge for n-1 edges; if so
//     that alone is O(n**2), independent of the DFS-style options loop
//     that also rewrites visited and colors the same way.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 53, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": ["IntToString", "ParseInt", "SplitWs",
//     "SumSeq"], "loop_depth": 1, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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
  requires n >= 0
  // same as 2854_107: a target is marked visited on pop, not on push.
  decreases *
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
    decreases *
  {
    var t := options[|options| - 1];
    options := options[..|options| - 1];
    var tgt := t.0;
    var src := t.1;
    if 0 <= tgt < |visited| && visited[tgt] == 0 {
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
