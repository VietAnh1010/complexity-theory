// 1197_B. Pillars  (problem 1453, solution 1453_211)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def f(l):
//     for i in range(len(l)-1):
//         if l[i] > l[i+1]:
//             break
//     #print(i+1)
//     if sorted(l[i+1:],reverse=True) == l[i+1:]:return 0
//     return 1
// 
// M = 10**9 + 7
// R = lambda: map(int, input().split())
// n = int(input())
// L = list(R())
// if len(set(L)) != n:print("NO")
// else:print("YNEOS"[f(L)::2])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var sortedL := SortInts(a_list);
  var hasDup := false;
  var j := 0;
  while j < |sortedL| - 1
    decreases |sortedL| - 1 - j
  {
    if sortedL[j] == sortedL[j+1] { hasDup := true; }
    j := j + 1;
  }
  if hasDup {
    output := "NO";
  } else {
    var i := 0;
    while i < n - 2 && !(a_list[i] > a_list[i+1])
      decreases n - 2 - i
    {
      i := i + 1;
    }
    // check a_list[i+1..n] non-increasing
    var nonInc := true;
    var p := i + 1;
    while p < n - 1
      decreases n - 1 - p
    {
      if a_list[p] < a_list[p+1] { nonInc := false; }
      p := p + 1;
    }
    output := if nonInc then "YES" else "NO";
  }
}
