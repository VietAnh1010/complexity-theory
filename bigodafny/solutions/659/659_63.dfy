// 127_B. Canvas Frames  (problem 659, solution 659_63)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int, input().split()))
// a.sort()
// b,t,c=[],1,0
// for i in range(n):
//     if i==n-1 or a[i]!=a[i+1]:
//         c+=t//4
//         if t%4>=2:b.append(t%2)
//         t=1
//     else:t+=1
// print(len(b)//2+c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, ratings: seq<int>) returns (output: string)
{
  var a := SortInts(ratings);
  var bLen := 0;
  var t := 1;
  var c := 0;
  var i := 0;
  while i < |a|
    decreases |a| - i
  {
    if i == |a| - 1 || a[i] != a[i+1] {
      c := c + t / 4;
      if t % 4 >= 2 { bLen := bLen + 1; }
      t := 1;
    } else {
      t := t + 1;
    }
    i := i + 1;
  }
  output := IntToString(bLen / 2 + c);
}
