// 999_A. Mishka and Contest  (problem 1470, solution 1470_470)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// arr=list(map(int, input().split(' ')))
// ar=list(map(int, input().split(' ')))
// t=0
// for i in range (arr[0]):
//     if ar[i]>arr[1]:
//         t=ar.index(ar[i])
//         break
// ar.reverse()
// z=0
// for each in ar:
//     if each>arr[1]:
//         z=ar.index(each)
//         break
// ar=sorted(ar)
// s=0
// for h in ar:
//     if h>arr[1]:
//         s=1
// if s==0:
//     print (arr[0])
// else:
//     print (z+t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  var idx1 := -1;
  var i := 0;
  while i < n && idx1 == -1
    decreases n - i
  {
    if a_list[i] > k { idx1 := i; }
    i := i + 1;
  }
  if idx1 == -1 {
    output := IntToString(n);
  } else {
    var idx2 := n - 1;
    var found2 := false;
    var j := n - 1;
    while j >= 0 && !found2
      decreases j + 1
    {
      if a_list[j] > k { idx2 := j; found2 := true; }
      j := j - 1;
    }
    output := IntToString(idx1 + (n - 1 - idx2));
  }
}
