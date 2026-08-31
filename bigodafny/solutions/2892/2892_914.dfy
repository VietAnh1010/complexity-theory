// 1228_A. Distinct Digits  (problem 2892, solution 2892_914)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b=map(int,input().split())
// r=[]
// flag=0
// for i in range(a,b+1):
//     tmp=i
//     r=[int(d) for d in str(i)]
//     s=set(r)
//     if(len(r)==len(s)):
//         flag=1
//         break
// if(flag):
//     print(tmp)
// else:
//     print("-1")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
