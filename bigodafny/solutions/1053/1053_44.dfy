// 605_A. Sorting Railway Cars  (problem 1053, solution 1053_44)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// p=list(map(int,input().split()))
// for i in range(n):
//     p[i]=[p[i],i]
// p.sort()
// b=1
// d=[]
// for i in range(n-1):
//     if p[i][1]<p[i+1][1]:
//         b+=1
//     else:
//         d.append(b)
//         b=1
// d.append(b)
// print(n-max(d))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, a_list: seq<int>) returns (output: string)
{
  var pairs := seq(|a_list|, i requires 0 <= i < |a_list| => (a_list[i], i));
  var sortedPairs := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  var idxSeq := seq(|sortedPairs|, i requires 0 <= i < |sortedPairs| => sortedPairs[i].1);
  var b := 1;
  var maxD := 0;
  var i := 0;
  while i < N - 1
    decreases N - 1 - i
  {
    if idxSeq[i] < idxSeq[i + 1] {
      b := b + 1;
    } else {
      if b > maxD { maxD := b; }
      b := 1;
    }
    i := i + 1;
  }
  if b > maxD { maxD := b; }
  output := IntToString(N - maxD);
}

