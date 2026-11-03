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

lemma SplitFromLen(s: string, i: nat, cur: string, acc: seq<string>)
  requires i <= |s|
  ensures SumLen(SplitWsFrom(s, i, cur, acc)) <= SumLen(acc) + |cur| + (|s| - i)
  ensures |SplitWsFrom(s, i, cur, acc)| <= |acc| + 1 + (|s| - i)
  decreases |s| - i
{
  if i >= |s| {
    if |cur| > 0 { SumLenSnoc(acc, cur); }
  } else if IsSpace(s[i]) {
    if |cur| > 0 { SumLenSnoc(acc, cur); }
    SplitFromLen(s, i + 1, "", if |cur| > 0 then acc + [cur] else acc);
  } else {
    SplitFromLen(s, i + 1, cur + [s[i]], acc);
  }
}

lemma SplitLen(s: string)
  ensures SumLen(SplitWs(s)) <= |s|
{
  SplitFromLen(s, 0, "", []);
}

lemma TwoTokens(toks: seq<string>)
  requires |toks| >= 2
  ensures |toks[0]| + |toks[1]| <= SumLen(toks)
{
  SumLenElem(toks[1..], 0);
}

ghost function SA(adj: seq<seq<(int, int)>>): nat
  decreases |adj|
{ if |adj| == 0 then 0 else |adj[0]| + SA(adj[1..]) }

lemma SAUpd(adj: seq<seq<(int, int)>>, u: nat, x: (int, int))
  requires u < |adj|
  ensures SA(adj[u := adj[u] + [x]]) == SA(adj) + 1
  decreases |adj|
{
  if u > 0 {
    SAUpd(adj[1..], u - 1, x);
    assert adj[u := adj[u] + [x]][1..] == adj[1..][u - 1 := adj[1..][u - 1] + [x]];
  } else {
    assert adj[0 := adj[0] + [x]][1..] == adj[1..];
  }
}

lemma SAElem(adj: seq<seq<(int, int)>>, u: nat)
  requires u < |adj|
  ensures |adj[u]| <= SA(adj)
  decreases |adj|
{
  if u > 0 { SAElem(adj[1..], u - 1); }
}

ghost function U(adj: seq<seq<(int, int)>>, vis: seq<int>, k: nat): nat
  requires |vis| == |adj| && k <= |adj|
  decreases k
{ if k == 0 then 0 else U(adj, vis, k - 1) + (if vis[k - 1] == 0 then |adj[k - 1]| else 0) }

lemma ULe(adj: seq<seq<(int, int)>>, vis: seq<int>, k: nat)
  requires |vis| == |adj| && k <= |adj|
  ensures U(adj, vis, k) <= SA(adj[..k])
  decreases k
{
  if k > 0 {
    ULe(adj, vis, k - 1);
    assert adj[..k - 1] == adj[..k][..k - 1];
    SALast(adj[..k]);
    assert adj[..k][k - 1] == adj[k - 1];
  }
}

lemma SALast(adj: seq<seq<(int, int)>>)
  requires |adj| >= 1
  ensures SA(adj) == SA(adj[..|adj| - 1]) + |adj[|adj| - 1]|
  decreases |adj|
{
  if |adj| > 1 {
    SALast(adj[1..]);
    assert adj[1..][..|adj| - 2] == adj[..|adj| - 1][1..];
  } else {
    assert adj[..0] == [];
  }
}

lemma UUpd(adj: seq<seq<(int, int)>>, vis: seq<int>, t: nat, k: nat)
  requires |vis| == |adj| && k <= |adj| && t < |adj|
  requires vis[t] == 0
  ensures U(adj, vis[t := 1], k) + (if t < k then |adj[t]| else 0) == U(adj, vis, k)
  decreases k
{
  if k > 0 { UUpd(adj, vis, t, k - 1); }
}

lemma ULeAll(adj: seq<seq<(int, int)>>, vis: seq<int>)
  requires |vis| == |adj|
  ensures U(adj, vis, |adj|) <= SA(adj)
{
  ULe(adj, vis, |adj|);
  assert adj[..|adj|] == adj;
}

lemma SAEmpty(adj: seq<seq<(int, int)>>)
  requires forall k :: 0 <= k < |adj| ==> |adj[k]| == 0
  ensures SA(adj) == 0
  decreases |adj|
{
  if |adj| > 0 { SAEmpty(adj[1..]); }
}

method Solve(n: int, edges: seq<string>) returns (output: string, ghost steps: nat)
  requires n >= 0
  // same as 2854_107: a target is marked visited on pop, not on push.
  ensures steps <= 12 * n + 60 * |edges| + 3 * SumLen(edges) + |output| + 20
{
  steps := 1;
  var adj: seq<seq<(int, int)>> := seq(n, _ => []);
  steps := steps + n + 1;
  SAEmpty(adj);
  var idx := 0;
  ghost var b := steps;
  while idx < |edges|
    invariant 0 <= idx <= |edges|
    invariant |adj| == n
    invariant SA(adj) <= 2 * idx
    invariant steps <= b + 10 * idx + 3 * SumLen(edges[..idx])
    decreases |edges| - idx
  {
    var toks := SplitWs(edges[idx]);
    SplitLen(edges[idx]);
    steps := steps + 10 + 3 * |edges[idx]|;
    ghost var sl := SumLen(edges[..idx]);
    assert edges[..idx + 1] == edges[..idx] + [edges[idx]];
    SumLenSnoc(edges[..idx], edges[idx]);
    if |toks| >= 2 {
      var u := ParseInt(toks[0]) - 1;
      var v := ParseInt(toks[1]) - 1;
      if 0 <= u < |adj| && 0 <= v < |adj| {
        SAUpd(adj, u, (v, u));
        adj := adj[u := adj[u] + [(v, u)]];
        SAUpd(adj, v, (u, v));
        adj := adj[v := adj[v] + [(u, v)]];
      }
    }
    idx := idx + 1;
  }
  assert edges[..|edges|] == edges;

  var visited: seq<int> := seq(n, _ => 0);
  var colors: seq<int> := seq(n, _ => 0);
  steps := steps + 2 * n + 2;
  if n > 0 {
    visited := visited[0 := 1];
  }
  var options: seq<(int, int)> := if n > 0 && |adj| > 0 then adj[0] else [];
  ULeAll(adj, visited);
  if n > 0 { SAElem(adj, 0); }
  ghost var W0 := |options| + 2 * U(adj, visited, |adj|);
  ghost var b2 := steps;
  while |options| > 0
    invariant |visited| == n
    invariant |colors| == n
    invariant |adj| == n
    invariant steps + 8 * (|options| + 2 * U(adj, visited, |adj|)) <= b2 + 8 * W0
    decreases |options| + 2 * U(adj, visited, |adj|)
  {
    var t := options[|options| - 1];
    options := options[..|options| - 1];
    var tgt := t.0;
    var src := t.1;
    steps := steps + 8;
    if 0 <= tgt < |visited| && visited[tgt] == 0 {
      UUpd(adj, visited, tgt, |adj|);
      visited := visited[tgt := 1];
      if 0 <= src < |colors| {
        colors := colors[tgt := 1 - colors[src]];
      }
      if 0 <= tgt < |adj| {
        options := options + adj[tgt];
        steps := steps + |adj[tgt]|;
      }
    }
  }

  var x := SumSeq(colors);
  steps := steps + n + 1;
  output := IntToString(x * (n - x) - n + 1);
  IntToStringDigits(x * (n - x) - n + 1);
  steps := steps + |output|;
}
