// 195_A. Let's Watch Football  (problem 1580, solution 1580_12)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b,c=map(int,input().split())
// val=b
// res=[val]
// i=2
// while(val<a*c):
//     val=b*i
//     res+=[val]
//     i+=1
// n=len(res)
// l=0
// h=n-1
// ans=-1
// #print(res)
// while(l<=h):
//     mid=l+(h-l)//2
//     if(res[mid]+b*(c-1)<a*c):
//         ans=mid
//         l=mid+1
//     else:
//         h=mid-1
//     #print(mid)
// print(ans+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
{
  var res: seq<int> := [b];
  var val := b;
  var it := 2;
  while val < a * c
    decreases a * c - val
  {
    val := b * it;
    res := res + [val];
    it := it + 1;
  }
  var l := 0;
  var h := |res| - 1;
  var ans := -1;
  while l <= h
    decreases h - l
  {
    var mid := l + (h - l) / 2;
    if res[mid] + b * (c - 1) < a * c {
      ans := mid;
      l := mid + 1;
    } else {
      h := mid - 1;
    }
  }
  output := IntToString(ans + 1);
}
