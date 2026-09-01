// 764_A. Taymyr is calling you  (problem 1738, solution 1738_180)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// abc= input().split()
// 
// a= int(abc[0])
// b= int(abc[1])
// c= int(abc[2])
// 
// d= c//a
// e=c//b
// test=[]
// test2=[]
// count=0
// for i in range(1,d+1):
//     test.append(i*a)
// 
// for i in range(1,e+1):
//     if i*b in test:
//         count=count+1
// 
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
{
  var d := c / a;
  var e := c / b;
  var test: seq<int> := [];
  var i := 1;
  while i <= d
    decreases d - i + 1
  {
    test := test + [i * a];
    i := i + 1;
  }
  var count := 0;
  i := 1;
  while i <= e
    decreases e - i + 1
  {
    var found := false;
    var k := 0;
    while k < |test|
      decreases |test| - k
    {
      if test[k] == i * b { found := true; }
      k := k + 1;
    }
    if found { count := count + 1; }
    i := i + 1;
  }
  output := IntToString(count);
}
