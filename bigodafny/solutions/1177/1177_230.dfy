// 785_B. Anton and Classes  (problem 1177, solution 1177_230)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l1=1000000005
// z2=1000000005
// l2=0
// z1=0
// for i in range(0,n):
//      x,y=input().split(" ")
//      x,y=int(x),int(y)
//      l1=min(y,l1)
//      z1=max(z1,x)
// m=int(input())
// for i in range(0,m):
//      x,y=input().split(" ")
//      x,y=int(x),int(y)
//      l2=max(x,l2)
//      z2=min(z2,y)
// o=max(z1-z2,l2-l1)
// if(o<0):
//      print("0")
// else :
//      print(o)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rectangles: seq<(int, int)>, m: int, checks: seq<(int, int)>) returns (output: string)
{
  var l1 := 1000000005;
  var z1 := 0;
  var z2 := 1000000005;
  var l2 := 0;
  var i := 0;
  while i < n
    decreases n - i
  {
    var x := rectangles[i].0;
    var y := rectangles[i].1;
    if y < l1 { l1 := y; }
    if x > z1 { z1 := x; }
    i := i + 1;
  }
  i := 0;
  while i < m
    decreases m - i
  {
    var x := checks[i].0;
    var y := checks[i].1;
    if x > l2 { l2 := x; }
    if y < z2 { z2 := y; }
    i := i + 1;
  }
  var o := z1 - z2;
  if l2 - l1 > o { o := l2 - l1; }
  if o < 0 {
    output := "0";
  } else {
    output := IntToString(o);
  }
}
