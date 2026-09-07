// 1155_C. Alarm Clocks Everywhere  (problem 1915, solution 1915_63)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def nod(a,b):
//     while a*b!=0:
//         if a>b:
//             a%=b
//         else:
//             b%=a
//     return a+b
// n,m=map(int,input().split())
// l=[int(j) for j in input().split()]
// p=[int(j) for j in input().split()]
// 
// nd=l[1]-l[0]
// ans=-1
// for i in range(2,n):
// 
//     nd=nod(nd,l[i]-l[i-1])
//     
// for i in range(m):
//    
//     if nd%p[i]==0:
//         ans=i
//         break
//     
// if ans==-1:
//     print('NO')
// else:
//     print('YES')
//     print(l[0],ans+1)
//     
// 
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, n_list: seq<int>, m_list: seq<int>) returns (output: string)
  requires n >= 2
  requires m >= 1
  requires |n_list| == n
  requires |m_list| == m
{
  var l := n_list;
  var p := m_list;
  var nd := AbsInt(l[1] - l[0]);
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant nd >= 0
  {
    nd := AbsInt(Gcd(nd, AbsInt(l[i] - l[i-1])));
    i := i + 1;
  }
  var ans := -1;
  var j := 0;
  while j < m
    invariant 0 <= j <= m
    invariant ans == -1 || (0 <= ans < j)
  {
    if p[j] != 0 && nd % p[j] == 0 {
      ans := j;
      break;
    }
    j := j + 1;
  }
  if ans == -1 {
    output := "NO\n";
  } else {
    output := "YES\n" + IntToString(l[0]) + " " + IntToString(ans+1) + "\n";
  }
}
