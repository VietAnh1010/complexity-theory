// 1155_C. Alarm Clocks Everywhere  (problem 1915, solution 1915_158)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// n,m=[int(i) for i in input().split()]
// x=[int(i) for i in input().split()]
// p=[int(i) for i in input().split()]
// x_2=[]
// for i in range(1,len(x)):
//     x_2.append(x[i]-x[i-1])
// g=x_2[0]
// for i in range(1,len(x_2)):
//     g=math.gcd(g,x_2[i])
// b=False
// for i in range (0,len(p)):
//     if(g%p[i]==0):
//         print('YES')
//         print(x[0],i+1)
//         b=True
//         break
// if(not(b)):     
//     print('NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, n_list: seq<int>, m_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
