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

method Solve(n: int, q: int, queries: seq<seq<int>>) returns (output: string)
  requires n >= 1
{
  var removed := seq(n + 1, i requires 0 <= i < n + 1 => false);
  var qi := 0;
  while qi < q && qi < |queries|
    invariant 0 <= qi
    invariant |removed| == n + 1
    decreases q - qi
  {
    var row := queries[qi];
    var k := 0;
    while k < |row|
      invariant 0 <= k <= |row|
      invariant |removed| == n + 1
      decreases |row| - k
    {
      var x := row[k];
      if 1 <= x <= n {
        removed := removed[x := true];
      }
      k := k + 1;
    }
    qi := qi + 1;
  }
  var a := 1;
  while a <= n && removed[a]
    invariant 1 <= a <= n + 1
    decreases n - a
  {
    a := a + 1;
  }
  var parts: seq<string> := [IntToString(n - 1) + "\n"];
  var i := 1;
  while i <= n
    invariant 1 <= i
    decreases n - i
  {
    if i != a {
      parts := parts + [IntToString(i) + " " + IntToString(a) + "\n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
