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

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

method Solve(a: int, b: int, c: int) returns (output: string, ghost steps: nat)
  requires b >= 1
  requires a >= 0
  requires c >= 0
  ensures steps <= 8 * (a * c) + 8 * b + |output| + 20
{
  var res: seq<int> := [b];
  var val := b;
  var it := 2;
  steps := 2;
  ghost var base1 := steps;
  ghost var cnt := 0;
  while val < a * c
    invariant it >= 2
    invariant val == b * (it - 1)
    invariant cnt == it - 2
    invariant val >= b * cnt
    invariant val <= a * c + b
    invariant |res| == cnt + 1
    invariant steps <= base1 + 3 * cnt
    decreases a * c - val
  {
    val := b * it;
    res := res + [val];
    it := it + 1;
    cnt := cnt + 1;
    steps := steps + 3;
  }
  // The loop only continues while val < a*c, and val grows by exactly b
  // (>= 1) each iteration, so cnt (the iteration count) is bounded by
  // roughly a*c/b -- loosely, by a*c itself since b >= 1.
  assert cnt <= a * c + 1;
  var l := 0;
  var h := |res| - 1;
  var ans := -1;
  ghost var base2 := steps;
  ghost var cnt2 := 0;
  ghost var span0 := h - l;
  while l <= h
    invariant 0 <= l
    invariant h <= |res| - 1
    invariant h - l <= span0 - cnt2
    invariant cnt2 <= span0 + 1
    invariant steps <= base2 + 2 * cnt2
    decreases h - l
  {
    var mid := l + (h - l) / 2;
    ghost var oldSpan := h - l;
    if res[mid] + b * (c - 1) < a * c {
      ans := mid;
      l := mid + 1;
      assert h - l <= oldSpan - 1;
    } else {
      h := mid - 1;
      assert h - l <= oldSpan - 1;
    }
    cnt2 := cnt2 + 1;
    steps := steps + 2;
  }
  assert cnt2 <= span0 + 1;
  assert span0 <= |res|;
  assert cnt2 <= |res| + 1;
  assert |res| <= a * c + 2;
  output := IntToString(ans + 1);
  steps := steps + |output| + 2;
}
