// 1234_B1. Social Network (easy version)  (problem 64, solution 64_609)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// a = [0] * k
// l = 0
// curr = set()
// 
// ids = map(int, input().split())
// 
// for id in ids:
//     if id not in curr:
//         curr.add(id)
// 
//         if a[-1] != 0:
//             curr.remove(a[-1])
// 
//         a[1:] = a[:-1]
//         a[0] = id
//         l = min(l + 1, k)
// 
// print(l)
// print(' '.join(map(str, a[:l])))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, ratings: seq<int>) returns (output: string)
{
  assume {:axiom} k >= 1;
  var a: seq<int> := seq(k, i => 0);
  var l := 0;
  var curr: set<int> := {};
  var idx := 0;
  while idx < |ratings|
    invariant |a| == k
    decreases |ratings| - idx
  {
    var id := ratings[idx];
    if id !in curr {
      curr := curr + {id};
      if a[k - 1] != 0 {
        curr := curr - {a[k - 1]};
      }
      a := [id] + a[..k - 1];
      l := if l + 1 < k then l + 1 else k;
    }
    idx := idx + 1;
  }
  output := IntToString(l) + "\n" + JoinInts(a[..l], " ");
}
