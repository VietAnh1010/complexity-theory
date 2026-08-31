// 998_A. Balloons  (problem 2225, solution 2225_154)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=list(map(int,input().split()))
// z=sorted(l)
// for i in range(n):
//   if(l[i]==z[0]):
//     mi=i
// if(n>2):
//   print(1)
//   print(mi+1)
// else:
//   if(n==2):
//     if(l[0]==l[1]):
//       print(-1)
//     else:
//       print(1)
//       print(1)
//   else:
//     print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, dimensions: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
