// 1216_D. Swords  (problem 1640, solution 1640_36)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n  = int(input())
// lis = sorted(map(int,input().split()),reverse = True)
// gg = 0
// aa=1
// ans=0
// for i in range(n):
//     gg = math.gcd(lis[0]-lis[i],gg)
// for i in range(n):
//     ans+=((lis[0]-lis[i])//gg)
// print(ans,gg)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var lis := Sort(a_list, (x: int, y: int) => x > y);
  var g := 0;
  var i := 0;
  while i < |lis|
    decreases |lis| - i
  {
    g := Gcd(lis[0] - lis[i], g);
    i := i + 1;
  }
  var ans := 0;
  i := 0;
  while i < |lis|
    decreases |lis| - i
  {
    ans := ans + (lis[0] - lis[i]) / g;
    i := i + 1;
  }
  output := IntToString(ans) + " " + IntToString(g);
}
