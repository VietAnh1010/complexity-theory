// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n*m)
//   cause          : unclear
//   confidence     : low
//   auditor        : main agent, override of labelaudit-r4-s04
//
//   Which of the label or the translation is at fault was not determined
//   by the audit.
//
//   evidence:
//     Override of labelaudit-r4-s04's mismatch: the only width the code
//     walks is each edge line's two numerals through SplitWs and ParseInt;
//     the DFS over the adjacency lists is O(n), so the class depends on
//     the open ParseInt charge.
//
//   how this label could be wrong, and what to check:
//     The verdict turns on whether a numeral token's width is a size. The
//     brief charges ParseInt its argument's length; the proofs (378_91,
//     976_1131) charge it 1, as IntToString is. Settle the ParseInt charge
//     in COMPLEXITY.md, then re-file: width as a size gives O(n*m), a
//     machine-word token gives O(n).
//
//   structural facts (deterministic, from label_audit.py):
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
