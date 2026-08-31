// 300_A. Array  (problem 1717, solution 1717_238)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #A. Array
// n = int(input())
// a,b,c =[],[],[]
// l = list(map(int,input().split()))
// for i in l:
//     if i<0:
//         a.append(i)
//     elif i>0:
//         b.append(i)
//     else:
//         c.append(i)
// 
// if len(b)==0 and len(a)>2:
//     b.append(a.pop())
//     b.append(a.pop()) 
// if len(a)%2==0:
//     c.append(a.pop())    
// print(len(a),*a)
// print(len(b),*b)
// print(len(c),*c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
