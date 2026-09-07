// 442_B. Andrey and Problem  (problem 2496, solution 2496_46)
// time complexity: O(n**2)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import bisect
// n=int(input())
// ls=list(map(float,input().split()))
// ls.sort()
// mx=ls[-1]
// idx=bisect.bisect_left(ls,0.5)
// if idx<n and ls[idx]<0.5:
//     idx+=1
// 
// res=0
// st=0
// while(st<idx-1):
//     temp=0
//     for i in range(st,idx):
//         t=1
//         for j in range(st,idx):
//             if i!=j:
//                 t=t*(1-ls[j])
//                 
//         temp+=t*ls[i]
//     res=max(res,temp)
//     st+=1
// res=max(res,mx)
// print("%.12f"%res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<real>) returns (output: string)
  requires |a_list| >= 1
{
  var ls := Sort(a_list, (x: real, y: real) => x < y);
  var m := |ls|;
  var mx := ls[m - 1];
  var idx := 0;
  while idx < m && ls[idx] < 0.5
    invariant 0 <= idx <= m
  {
    idx := idx + 1;
  }
  if idx < m && ls[idx] < 0.5 {
    idx := idx + 1;
  }

  var res: real := 0.0;
  var st := 0;
  while st < idx - 1
    invariant 0 <= st
  {
    var temp: real := 0.0;
    var i := st;
    while i < idx
      invariant st <= i <= idx
    {
      var t: real := 1.0;
      var j := st;
      while j < idx
        invariant st <= j <= idx
      {
        if i != j {
          t := t * (1.0 - ls[j]);
        }
        j := j + 1;
      }
      temp := temp + t * ls[i];
      i := i + 1;
    }
    if temp > res { res := temp; }
    st := st + 1;
  }
  if mx > res { res := mx; }

  var scaled := (res * 1000000000000.0 + 0.5).Floor;
  var digits := IntToString(scaled);
  while |digits| < 13 { digits := "0" + digits; }
  var intStr := digits[..|digits| - 12];
  var fracStr := digits[|digits| - 12..];
  output := intStr + "." + fracStr + "\n";
}
