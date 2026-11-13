// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Building adj does one SplitWs/ParseInt per edge with O(1) seq
//     updates, and the DFS pops each node once and loops over its
//     neighbour list, so over a tree the total work is O(n) (the sum of
//     degrees is 2(n-1)). The Python's data[u].append and stk loop do the
//     same, so it is linear and the O(n**2) label is wrong. Parsing each
//     edge string was treated as constant width.
//
//   how this label could be wrong, and what to check:
//     The label may assume the DFS rescans neighbours repeatedly. Check
//     the stack loop: the comment says nodes can be pushed more than once,
//     but in a tree a node's only unvisited neighbours are its children,
//     so each node is pushed once and the total pushes equal n.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 58, "data_dependent_loops": 1, "decreases_star":
//     true, "linear_prelude_calls": ["IntToString", "ParseInt",
//     "SplitWs"], "loop_depth": 2, "loops": 3, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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

ghost function Unvisited(s: seq<bool>): nat
  decreases |s|
{
  if |s| == 0 then 0 else (if s[0] then 0 else 1) + Unvisited(s[1..])
}

lemma UnvisitedUpd(s: seq<bool>, i: int)
  requires 0 <= i < |s| && !s[i]
  ensures Unvisited(s[i := true]) + 1 == Unvisited(s)
  decreases |s|
{
  if i > 0 {
    assert s[i := true][1..] == s[1..][i - 1 := true];
    UnvisitedUpd(s[1..], i - 1);
  } else {
    assert s[i := true][1..] == s[1..];
  }
}

ghost predicate FreshTop(stack: seq<(int, int)>, visited: seq<bool>)
{
  |stack| > 0 && 0 <= stack[|stack| - 1].0 < |visited| && !visited[stack[|stack| - 1].0]
}

method Solve(n: int, edges: seq<string>) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 40 * (|edges| + n + 2) + 6 * |edges| * (n + 2)
  // the DFS stack can hold a node more than once: a neighbour is marked
  // visited when popped, not when pushed. A pop that pushes leaves an
  // unvisited node on top, so the next pop visits it.
{
  steps := 1;
  var adj: seq<seq<int>> := seq(n + 1, _ => []);
  var idx := 0;
  while idx < |edges|
    invariant 0 <= idx <= |edges|
    invariant steps <= 1 + 40 * idx
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
    steps := steps + 40;
    idx := idx + 1;
  }

  var visited: seq<bool> := seq(n + 1, _ => false);
  var l0 := 0;
  var l1 := 0;
  var stack: seq<(int, int)> := [(1, 0)];
  while |stack| > 0
    invariant |visited| == n + 1
    invariant |adj| == n + 1
    invariant steps <= 1 + 40 * |edges| + 6 * (|edges| + 1) * (n + 2) - 6 * |stack|
    decreases Unvisited(visited), (if FreshTop(stack, visited) then 0 else 1), |stack|
  {
    steps := steps + 10;
    ghost var fresh0 := FreshTop(stack, visited);
    ghost var u0 := Unvisited(visited);
    var top := stack[|stack| - 1];
    stack := stack[..|stack| - 1];
    var node := top.0;
    var color := top.1;
    if 0 <= node < |visited| {
      if !visited[node] {
        UnvisitedUpd(visited, node);
      } else {
        assert visited[node := true] == visited;
      }
      visited := visited[node := true];
    }
    assert fresh0 ==> Unvisited(visited) < u0;
    assert !fresh0 ==> Unvisited(visited) == u0;
    ghost var len0 := |stack|;
    if color == 0 { l0 := l0 + 1; } else { l1 := l1 + 1; }
    if 0 <= node < |adj| {
      var nbrs := adj[node];
      var k := 0;
      while k < |nbrs|
        invariant 0 <= k <= |nbrs|
        invariant |stack| >= len0
        invariant |stack| > len0 ==> FreshTop(stack, visited)
        decreases |nbrs| - k
      {
        steps := steps + 6;
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
