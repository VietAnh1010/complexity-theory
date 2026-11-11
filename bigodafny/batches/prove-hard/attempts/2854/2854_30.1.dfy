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

include "../../../../prelude.dfy"

ghost function Sp(a: seq<seq<(int, int)>>, k: nat): nat
  requires k <= |a|
  decreases k
{
  if k == 0 then 0 else Sp(a, k - 1) + |a[k - 1]|
}

lemma SpUpd(a: seq<seq<(int, int)>>, u: int, x: seq<(int, int)>, k: nat)
  requires k <= |a| && 0 <= u < |a|
  ensures Sp(a[u := x], k) + (if u < k then |a[u]| else 0) == Sp(a, k) + (if u < k then |x| else 0)
  decreases k
{
  if k > 0 { SpUpd(a, u, x, k - 1); }
}

lemma SpElem(a: seq<seq<(int, int)>>, t: nat, k: nat)
  requires k <= |a| && t < k
  ensures |a[t]| <= Sp(a, k)
  decreases k
{
  if t < k - 1 { SpElem(a, t, k - 1); }
}

ghost function Wp(v: seq<int>, a: seq<seq<(int, int)>>, k: nat): nat
  requires k <= |v| && k <= |a|
  decreases k
{
  if k == 0 then 0 else Wp(v, a, k - 1) + (if v[k - 1] == 0 then 1 + |a[k - 1]| else 0)
}

lemma WpVisit(v: seq<int>, a: seq<seq<(int, int)>>, t: int, k: nat)
  requires k <= |v| && |v| == |a| && 0 <= t < |v| && v[t] == 0
  ensures Wp(v[t := 1], a, k) + (if t < k then 1 + |a[t]| else 0) == Wp(v, a, k)
  decreases k
{
  if k > 0 { WpVisit(v, a, t, k - 1); }
}

lemma WpBound(v: seq<int>, a: seq<seq<(int, int)>>, k: nat)
  requires k <= |v| && k <= |a|
  ensures Wp(v, a, k) <= k + Sp(a, k)
  decreases k
{
  if k > 0 { WpBound(v, a, k - 1); }
}

lemma SplitWsSum(s: string, i: nat, cur: string, acc: seq<string>)
  ensures SumLen(SplitWsFrom(s, i, cur, acc)) <= SumLen(acc) + |cur| + (if i <= |s| then |s| - i else 0)
  decreases |s| - i
{
  if i < |s| {
    if IsSpace(s[i]) {
      if |cur| > 0 { SumLenSnoc(acc, cur); }
    }
    SplitWsSum(s, i + 1, if IsSpace(s[i]) then "" else cur + [s[i]],
               if IsSpace(s[i]) then (if |cur| > 0 then acc + [cur] else acc) else acc);
  } else {
    if |cur| > 0 { SumLenSnoc(acc, cur); }
  }
}

lemma PrefixStep(edges: seq<string>, idx: nat)
  requires idx < |edges|
  ensures SumLen(edges[..idx + 1]) == SumLen(edges[..idx]) + |edges[idx]|
{
  assert edges[..idx + 1] == edges[..idx] + [edges[idx]];
  SumLenSnoc(edges[..idx], edges[idx]);
}

method Solve(n: int, edges: seq<string>)
    returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 70 * n + 230 * |edges| + 3 * SumLen(edges) + 20 + |output|
{
  steps := 0;
  steps := steps + n;
  var adj: seq<seq<(int, int)>> := seq(n, _ /* _v0 */ => []);
  var idx := 0;
  while idx < |edges|
    invariant 0 <= idx <= |edges|
    invariant |adj| == n
    invariant steps <= n + 30 * idx + 3 * SumLen(edges[..idx])
    invariant Sp(adj, n) <= 2 * idx
    decreases |edges| - idx
  {
    PrefixStep(edges, idx);
    steps := steps + 3;
    steps := steps + (1 + |edges[idx]|);
    var toks := SplitWs(edges[idx]);
    SplitWsSum(edges[idx], 0, "", []);
    steps := steps + 2;
    if |toks| >= 2 {
      SumLenElem(toks, 0);
      SumLenElem(toks, 1);
      steps := steps + (2 + |toks[0]|);
      var u := ParseInt(toks[0]) - 1;
      steps := steps + (2 + |toks[1]|);
      var v := ParseInt(toks[1]) - 1;
      steps := steps + (5 + if 0 <= u < |adj| then 4 else 0);
      if 0 <= u < |adj| && 0 <= v < |adj| {
        steps := steps + (4 + |[(v, u)]|);
        SpUpd(adj, u, adj[u] + [(v, u)], n);
        adj := adj[u := adj[u] + [(v, u)]];
        steps := steps + (4 + |[(u, v)]|);
        SpUpd(adj, v, adj[v] + [(u, v)], n);
        adj := adj[v := adj[v] + [(u, v)]];
      }
    }
    steps := steps + 1;
    idx := idx + 1;
  }
  assert edges[..|edges|] == edges;
  steps := steps + 2;
  steps := steps + n;
  var visited: seq<int> := seq(n, _ /* _v1 */ => 0);
  steps := steps + n;
  var colors: seq<int> := seq(n, _ /* _v2 */ => 0);
  steps := steps + 1;
  if n > 0 {
    steps := steps + 1;
    visited := visited[0 := 1];
  }
  steps := steps + (3 + (if n > 0 then 2 else 0) + if n > 0 && |adj| > 0 then 1 else 0);
  var options: seq<(int, int)> := if n > 0 && |adj| > 0 then adj[0] else [];
  WpBound(visited, adj, n);
  if n > 0 { SpElem(adj, 0, n); }
  ghost var steps0 := steps;
  ghost var P0 := |options| + 2 * Wp(visited, adj, n);
  while |options| > 0
    invariant |visited| == n
    invariant |colors| == n
    invariant |adj| == n
    invariant steps + 32 * (|options| + 2 * Wp(visited, adj, n)) <= steps0 + 32 * P0
    decreases |options| + 2 * Wp(visited, adj, n)
  {
    ghost var sB := steps;
    ghost var oB := |options|;
    ghost var wB := Wp(visited, adj, n);
    steps := steps + 3;
    steps := steps + 3;
    var t := options[|options| - 1];
    steps := steps + 3;
    options := options[..|options| - 1];
    steps := steps + 1;
    var tgt := t.0;
    steps := steps + 1;
    var src := t.1;
    steps := steps + (5 + if 0 <= tgt < |visited| then 2 else 0);
    if 0 <= tgt < |visited| && visited[tgt] == 0 {
      steps := steps + 1;
      WpVisit(visited, adj, tgt, n);
      visited := visited[tgt := 1];
      steps := steps + 4;
      if 0 <= src < |colors| {
        steps := steps + 3;
        colors := colors[tgt := 1 - colors[src]];
      }
      steps := steps + 4;
      if 0 <= tgt < |adj| {
        steps := steps + (1 + |adj[tgt]|);
        options := options + adj[tgt];
      }
    }
  }
  steps := steps + 2;
  steps := steps + |colors|;
  var x := SumSeq(colors);
  steps := steps + (4 + Digits(x * (n - x) - n + 1));
  IntToStringDigits(x * (n - x) - n + 1);
  output := IntToString(x * (n - x) - n + 1);
}

import opened Prelude
