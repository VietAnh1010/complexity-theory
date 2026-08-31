// 450_A. Jzzhu and Children  (problem 2992, solution 2992_87)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n,m = map(int,input().split())
// a = list(map(int,input().split()))
// cc = math.ceil(a[0]/m)
// for i in range (len(a)):
//     if( math.ceil(a[i]/m) >= cc ):
//         x=i+1
//         cc = math.ceil(a[i]/m)
//         
// print(x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
