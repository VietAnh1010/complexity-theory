// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+mlogm)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both the Python (`c=b[:k]; c.sort(key=...)`) and the Dafny
//     (`c:=bSorted[..kk]; cSorted:=Sort(c,...)`) re-sort up to kk<=n
//     elements inside the per-query loop of q iterations, giving
//     worst-case O(q*n*log n), not O(n+m log m); this is a naive
//     resort-per-query approach in both sources, so the Python itself is
//     already outside the labelled class.
//
//   how this label could be wrong, and what to check:
//     The label implies each query is answered in roughly O(log n) or O(1)
//     after one O(n log n) preprocessing sort. Open the query loop and
//     check that `c := bSorted[..kk]` then `cSorted := Sort(c,...)`
//     re-sorts up to kk<=n elements on every one of the q queries; if
//     queries can have kk close to n (the description only bounds
//     1<=k<=n), the per-query cost is O(n log n), not O(log m), making the
//     whole loop O(q*n*log n).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 28, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["Sort"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 1261_B1. Optimal Subsequences (Easy Version)  (problem 1338, solution 1338_48)
// time complexity: O(n+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(i) for i in input().split()]
// b = [(a[i], n - i) for i in range(n)]
// b.sort(reverse=True)
// b = [(b[i][0], n - b[i][1]) for i in range(n)]
// 
// m = int(input())
// for qu in range(m):
//     k, p = map(int, input().split())
//     c = b[:k]
//     c.sort(key = lambda x: x[1])
//     print(c[p-1][0])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, q: int, queries: seq<(int, int)>) returns (output: string)
  requires n >= 0
  requires n == |a_list|
  requires q == |queries|
  requires forall t :: 0 <= t < q ==> 1 <= queries[t].0 <= n && 1 <= queries[t].1 <= queries[t].0
{
{

  var b0 := seq(n, idx requires 0 <= idx < n => (a_list[idx], idx));
  var bSorted := Sort(b0, (x: (int, int), y: (int, int)) =>
    if x.0 != y.0 then x.0 > y.0 else x.1 < y.1);
  var results: seq<string> := [];
  var i := 0;
  while i < q
    invariant 0 <= i <= q
    decreases q - i
  {
    var kk := queries[i].0;
    var p := queries[i].1;
    var c := bSorted[..kk];
    var cSorted := Sort(c, (x: (int, int), y: (int, int)) => x.1 < y.1);
    results := results + [IntToString(cSorted[p-1].0)];
    i := i + 1;
  }
  output := Join(results, "\n");
}
}
