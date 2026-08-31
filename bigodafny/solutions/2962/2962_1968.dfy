// 141_A. Amusing Joke  (problem 2962, solution 2962_1968)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=input()
// l=input()
// m=input()
// a=len(n)+len(l)
// c=0
// n=list(n)+list(l)
// m=list(m)
// d=[]
// d=d+m
// for i in range(len(n)):
//     if n[i] not in m:
//         c=1
//         break
//     else:
//         d.remove(n[i])
//         m.remove(n[i])
// if c==1:
//     print("NO")
// elif len(d)!=0:
//     print("NO")
// else:
//     print("YES")
//             
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(first_name: seq<string>, second_name: seq<string>, jumbled_name: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
