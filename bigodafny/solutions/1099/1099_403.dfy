// 937_A. Olympiad  (problem 1099, solution 1099_403)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a=int(input())
// b=list(map(int, input().split()))
// x=[]
// for i in b:
//   if i!=0:
//     x. append(i)
// 
//     
// 
// print(len(set(x)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var s: set<int> := {};
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    if a_list[i] != 0 { s := s + {a_list[i]}; }
    i := i + 1;
  }
  output := IntToString(|s|);
}

