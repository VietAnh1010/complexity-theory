// 1228_A. Distinct Digits  (problem 2892, solution 2892_1216)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x,y=map(int,input().split())
// for i in range(x,y+1,1):
//   l=[]
//   temp=i
//   while temp>0:
//       r=temp%10
//       l.append(r)
//       temp=temp//10
//   s=set(l) 
//   a=len(s)
//   b=len(l)
//   if a==b:
//       print(i)
//       break
// if a!=b:
//      print('-1')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var found := false;
  var ans := 0;
  var i := a;
  while i <= b && !found
    invariant a <= i
    decreases b - i + 1
  {
    var temp := i;
    var digits: seq<int> := [];
    while temp > 0
      decreases temp
    {
      digits := digits + [temp % 10];
      temp := temp / 10;
    }
    var distinct := true;
    var p := 0;
    while p < |digits|
      invariant 0 <= p <= |digits|
      decreases |digits| - p
    {
      var q := p + 1;
      while q < |digits|
        invariant p < q <= |digits|
        decreases |digits| - q
      {
        if digits[p] == digits[q] { distinct := false; }
        q := q + 1;
      }
      p := p + 1;
    }
    if distinct {
      found := true;
      ans := i;
    }
    i := i + 1;
  }
  if found {
    output := IntToString(ans);
  } else {
    output := "-1";
  }
}
