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

function GcdNN(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures GcdNN(a, b) >= 0
  ensures GcdNN(a, b) == Gcd(a, b)
  decreases b
{
  if b == 0 then a else GcdNN(b, a % b)
}

method Solve(n: int, m: int, n_list: seq<int>, m_list: seq<int>) returns (output: string)
  requires n >= 2
  requires m >= 0
  requires |n_list| >= n
  requires |m_list| >= m
  requires forall t :: 0 <= t < |m_list| ==> m_list[t] >= 1
{
  var g := AbsInt(n_list[1] - n_list[0]);
  var i := 2;
  while i < n
    invariant 0 <= i
    invariant g >= 0
    decreases n - i
  {
    g := GcdNN(g, AbsInt(n_list[i] - n_list[i - 1]));
    i := i + 1;
  }
  var found := false;
  var idx := 0;
  var j := 0;
  while j < m && !found
    invariant 0 <= j
    decreases m - j
  {
    if g % m_list[j] == 0 {
      found := true;
      idx := j;
    }
    j := j + 1;
  }
  if found {
    output := "YES\n" + IntToString(n_list[0]) + " " + IntToString(idx + 1);
  } else {
    output := "NO";
  }
}
