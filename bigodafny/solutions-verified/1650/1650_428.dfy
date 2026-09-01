// 248_A. Cupboards  (problem 1650, solution 1650_428)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #!/usr/bin/env python3
// # -*- coding: utf-8 -*-
// n=int(input())
// d=[]
// l,p,t=0,0,0,
// for i in range(n):
//     d.append(list(map(int,input().split())))
//     if d[i][0]==1:
//         l+=1
//     if d[i][1]==1:
//         p+=1
// if l<n-l:
//     t+=l
// else:
//     t+=n-l
// if p<n-p:
//     t+=p
// else:
//     t+=n-p
// print(t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<string>>) returns (output: string)
{
  var l := 0;
  var p := 0;
  var i := 0;
  while i < |pairs|
    decreases |pairs| - i
  {
    if pairs[i][0] == "1" { l := l + 1; }
    if pairs[i][1] == "1" { p := p + 1; }
    i := i + 1;
  }
  var t1 := if l < n - l then l else n - l;
  var t2 := if p < n - p then p else n - p;
  output := IntToString(t1 + t2);
}
