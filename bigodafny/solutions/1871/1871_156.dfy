// 1349_A. Orac and LCM  (problem 1871, solution 1871_156)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import gcd
//  
// n = int(input())
// lst = list(map(int, input().split()))
// 
// lst.sort()
//  
// g = gcd(lst[0],lst[1])
// l = int((lst[0]*lst[1])/(g))
//  
// for i in range(2,n):
//     l = gcd(l , int((lst[i]*g)/gcd(g,lst[i])))
//     g = gcd(g, lst[i])
//     
// print(l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var lst := SortInts(a_list);
  var g := Gcd(lst[0], lst[1]);
  var l := (lst[0] * lst[1]) / g;
  var i := 2;
  while i < n
    decreases n - i
  {
    var gi := Gcd(g, lst[i]);
    var running := (lst[i] * g) / gi;
    l := Gcd(l, running);
    g := Gcd(g, lst[i]);
    i := i + 1;
  }
  output := IntToString(l);
}
