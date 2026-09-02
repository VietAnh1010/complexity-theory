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
{
{

  var b0 := seq(n, idx requires 0 <= idx < n => (a_list[idx], idx));
  var bSorted := Sort(b0, (x: (int, int), y: (int, int)) =>
    if x.0 != y.0 then x.0 > y.0 else x.1 < y.1);
  var results: seq<string> := [];
  var i := 0;
  while i < q
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
