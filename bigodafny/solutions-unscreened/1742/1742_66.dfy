// p03214 Dwango Programming Contest V - Thumbnail  (problem 1742, solution 1742_66)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int, input().split()))
// mean=sum(a)/n
// a=[abs(i-mean) for i in a]
// b=[]
// for i in range(n):
//     b.append([a[i],i])
// b.sort()
// print(b[0][1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 1 && |a_list| == n
{
  var total := SumSeq(a_list);
  // a[i] = |a_list[i] - mean| scaled by n; b = [a[i], i] pairs
  var b: seq<(int, int)> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |b| == i
    decreases n - i
  {
    b := b + [(AbsInt(a_list[i] * n - total), i)];
    i := i + 1;
  }
  b := Sort(b, (p: (int, int), q: (int, int)) => p.0 < q.0 || (p.0 == q.0 && p.1 < q.1));
  output := IntToString(b[0].1);
}
