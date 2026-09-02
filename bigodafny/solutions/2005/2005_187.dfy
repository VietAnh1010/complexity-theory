// 1051_C. Vasya and Multisets  (problem 2005, solution 2005_187)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import *
// n = int(input())
// a = list(map(int,input().split()))
// ans = ["A"]*n
// num = 0
// for i in range(n):
//     if a.count(a[i])>1:
//         continue
//     if num<0:
//         num+=1
//         ans[i] = "B"
//     else:
//         num-=1
// if num<0:
//     for i in range(n):
//         if a.count(a[i])<=2:
//             continue
//         ans[i] = "B"
//         num= 0
//         break
// if num==0:
//     print("YES")
//     print(*ans,sep = '')
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var ans: seq<char> := Repeat("A", n as nat);
  var num := 0;
  var i := 0;
  while i < n
    decreases n - i
  {
    var cnt := CountOcc2005(numbers, numbers[i]);
    if cnt <= 1 {
      if num < 0 {
        num := num + 1;
        ans := ans[i := 'B'];
      } else {
        num := num - 1;
      }
    }
    i := i + 1;
  }
  if num < 0 {
    var j := 0;
    var stop := false;
    while j < n && !stop
      decreases n - j
    {
      var cnt2 := CountOcc2005(numbers, numbers[j]);
      if cnt2 > 2 {
        ans := ans[j := 'B'];
        num := 0;
        stop := true;
      }
      j := j + 1;
    }
  }
  if num == 0 {
    output := "YES\n" + ans;
  } else {
    output := "NO";
  }
}

method CountOcc2005(a: seq<int>, x: int) returns (c: int)
{
  c := 0;
  var i := 0;
  while i < |a|
    decreases |a| - i
  {
    if a[i] == x {
      c := c + 1;
    }
    i := i + 1;
  }
}
