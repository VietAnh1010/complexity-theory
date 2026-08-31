// 24_A. Ring road  (problem 348, solution 348_21)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// source=set()
// dest=set()
// c1=0
// c2=0
// for i in range(int(input())):
//     s,d,w=map(int,input().split())
//     if s in source or d in dest:
//         c1=c1+w
//         s,d=d,s
//     else:
//         c2=c2+w
//     source.add(s)
//     dest.add(d)
// print(min(c1,c2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, v_list: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
