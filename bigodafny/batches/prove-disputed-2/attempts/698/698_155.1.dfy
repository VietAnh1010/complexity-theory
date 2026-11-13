// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n+m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny initialises `removed` of length n + 1, loops over the q
//     forbidden pairs marking each, then scans 1..n, O(n + m); the Python
//     likewise builds a set of n cities and subtracts m pairs.
//
//   how this label could be wrong, and what to check:
//     The label names only the city count n, but both programs also loop
//     over the m forbidden pairs. Check that m is read from input as a
//     separate count (the pair loop `for _ in range(m)` and the Dafny's
//     `while qi < q`); then the class is O(n+m).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 47, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 2, "loops": 4, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 330_B. Road Construction  (problem 698, solution 698_155)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// func = lambda: map(int, input().split())
// n, m = func()
// a = set(range(1, n+1))
// for _ in range(m): a-=set(func())
// a = list(a)[0]
// print(n-1)
// for i in range(1, n+1):
//     if i!=a: print(i, a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function RowsLen(m: seq<seq<int>>, k: nat): nat
  requires k <= |m|
  decreases k
{
  if k == 0 then 0 else RowsLen(m, k - 1) + |m[k - 1]|
}

ghost function Cap(q: int, l: nat): nat
{
  if q < 0 then 0 else if q < l then q else l
}

method Solve(n: int, q: int, queries: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= 12 * Cap(q, |queries|) + 12 * RowsLen(queries, Cap(q, |queries|)) + 20 * n + 3 * |output| + 30
{
  var removed := seq(n + 1, i requires 0 <= i < n + 1 => false);
  steps := n + 2;
  var qi := 0;
  while qi < q && qi < |queries|
    invariant 0 <= qi <= Cap(q, |queries|)
    invariant |removed| == n + 1
    invariant steps <= n + 2 + 12 * qi + 12 * RowsLen(queries, qi)
    decreases q - qi
  {
    ghost var st0 := steps;
    var row := queries[qi];
    var k := 0;
    steps := steps + 4;
    while k < |row|
      invariant 0 <= k <= |row|
      invariant |removed| == n + 1
      invariant steps <= st0 + 4 + 12 * k
      decreases |row| - k
    {
      var x := row[k];
      if 1 <= x <= n {
        removed := removed[x := true];
      }
      k := k + 1;
      steps := steps + 12;
    }
    qi := qi + 1;
    steps := steps + 2;
    assert RowsLen(queries, qi) == RowsLen(queries, qi - 1) + |queries[qi - 1]|;
  }
  assert qi <= Cap(q, |queries|);
  var a := 1;
  ghost var st1 := steps;
  while a <= n && removed[a]
    invariant 1 <= a <= n + 1
    invariant steps <= st1 + 6 * (a - 1)
    decreases n - a
  {
    a := a + 1;
    steps := steps + 6;
  }
  var parts: seq<string> := [IntToString(n - 1) + "\n"];
  IntToStringDigits(n - 1);
  steps := steps + 6 + 2 * Digits(n - 1) + 2;
  SumLenSnoc([], IntToString(n - 1) + "\n");
  ghost var base := steps;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant |parts| <= i
    invariant steps <= base + 12 * (i - 1) + 2 * SumLen(parts)
    decreases n - i
  {
    if i != a {
      IntToStringDigits(i); IntToStringDigits(a);
      var p := IntToString(i) + " " + IntToString(a) + "\n";
      SumLenSnoc(parts, p);
      parts := parts + [p];
      steps := steps + 2 * |p| + 4;
    }
    i := i + 1;
    steps := steps + 8;
  }
  output := Join(parts, "");
  JoinLen(parts, "");
  steps := steps + SumLen(parts) + |parts|;
}
