// 903_C. Boxes Packing  (problem 1857, solution 1857_103)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=sorted(list(map(int,input().split())))
// d={}
// for i in a:
//     if i not in d:
//         d[i]=1
//     else:
//         d[i]+=1
// print(max(d.values()))
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
