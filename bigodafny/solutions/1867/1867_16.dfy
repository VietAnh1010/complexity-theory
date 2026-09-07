// 1202_D. Print a 1337-string...  (problem 1867, solution 1867_16)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import bisect
// 
// Q=int(input())
// 
// A=[n*(n-1)//2 for n in range(10**5)]
// 
// 
// x=bisect.bisect(A,10**9)
// 
// 
// for testcases in range(Q):
//     t=int(input())
// 
//     if t==1:
//         print(1337)
//         continue
// 
//     x=bisect.bisect_left(A,t)
// 
//     ANS="1"+"3"*(x-1-2)+"1"*(t-(A[x-1]))+"337"
// 
//     print(ANS)
//     
//     
//     
//     
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
  requires n >= 0
  requires |numbers| >= n
{
  var lines: seq<string> := [];
  var qi := 0;
  while qi < n
    invariant 0 <= qi <= n
    decreases n - qi
  {
    var t := numbers[qi];
    if t == 1 {
      lines := lines + ["1337"];
    } else {
      var lo := 0;
      var hi := 100000;
      while lo < hi
        invariant 0 <= lo <= hi <= 100000
        decreases hi - lo
      {
        var mid := (lo + hi) / 2;
        if mid * (mid - 1) / 2 < t {
          lo := mid + 1;
        } else {
          hi := mid;
        }
      }
      var x := lo;
      var threes := x - 1 - 2;
      var threesN := if threes < 0 then 0 else threes;
      var aXm1 := (x - 1) * (x - 2) / 2;
      var ones := t - aXm1;
      var onesN := if ones < 0 then 0 else ones;
      var ans := "1" + Repeat("3", threesN) + Repeat("1", onesN) + "337";
      lines := lines + [ans];
    }
    qi := qi + 1;
  }
  output := Join(lines, "\n");
}
