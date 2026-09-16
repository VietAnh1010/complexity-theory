// 1228_A. Distinct Digits  (problem 2892, solution 2892_914)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b=map(int,input().split())
// r=[]
// flag=0
// for i in range(a,b+1):
//     tmp=i
//     r=[int(d) for d in str(i)]
//     s=set(r)
//     if(len(r)==len(s)):
//         flag=1
//         break
// if(flag):
//     print(tmp)
// else:
//     print("-1")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var flag := false;
  var tmp := 0;
  var i := a;
  while i <= b && !flag
    invariant a <= i
    decreases b - i + 1
  {
    tmp := i;
    var temp := i;
    var digits: seq<int> := [];
    if temp == 0 {
      digits := [0];
    } else {
      while temp > 0
        decreases temp
      {
        digits := digits + [temp % 10];
        temp := temp / 10;
      }
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
    if distinct { flag := true; }
    i := i + 1;
  }
  if flag {
    output := IntToString(tmp);
  } else {
    output := "-1";
  }
}
