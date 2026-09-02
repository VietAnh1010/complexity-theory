// 214_A. System of Equations  (problem 482, solution 482_366)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// k=list(map(int,input().split()))
// n=max(k)
// m=min(k)
// p=0
// for b in range(0,n+1):
//     if b<=n:
//         a=math.sqrt(n-b)
//         if m>=a:
//             if b==math.sqrt(m-a):
//                 if int(b)==b and int(a)==a:
//                     p+=1
// print(p)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var n := if a > b then a else b;
  var m := if a < b then a else b;
  var count := 0;
  var av := 0;
  while av <= n
    decreases n - av
  {
    var bv := 0;
    while bv <= n
      decreases n - bv
    {
      if av * av + bv == n && av + bv * bv == m {
        count := count + 1;
      }
      bv := bv + 1;
    }
    av := av + 1;
  }
  output := IntToString(count);
}
