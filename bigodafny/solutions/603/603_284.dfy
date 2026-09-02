// 1041_A. Heist  (problem 603, solution 603_284)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=list(map(int,input().split()))
// l.sort()
// x=0
// for i in range(n-1):
//     x+=l[i+1]-l[i]-1
// print(x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
  requires |numbers| == n
{

  var l := SortInts(numbers);
  var x := 0;
  var i := 0;
  while i < n - 1
    invariant 0 <= i
    invariant |l| == n
    decreases n - i
  {
    x := x + l[i+1] - l[i] - 1;
    i := i + 1;
  }
  output := IntToString(x);
}
