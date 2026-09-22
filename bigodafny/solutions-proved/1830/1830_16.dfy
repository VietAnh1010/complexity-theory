// 834_B. The Festive Evening  (problem 1830, solution 1830_16)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// s=input()
// m=0
// a=[0]*30
// b=[0]*30
// for i in s:
//     q=ord(i)-65
//     a[q]+=1
// for i in s:
//     q=ord(i)-65
//     if a[q]>0:
//         if b[q]==0:
//             if k==0:
//                 m=1
//                 break
//             b[q]=1
//             k-=1
//         a[q]-=1
//         if a[q]==0:
//             k+=1
//             b[q]=1
// if m==0:
//     print("NO")
// else:
//     print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, string_: string) returns (output: string, ghost steps: nat)
  requires forall t :: 0 <= t < |string_| ==> 'A' <= string_[t] <= 'Z'
  ensures steps <= 12 * |string_| + 12
{
  steps := 1;
  var a := seq(30, _ => 0);
  var b := seq(30, _ => 0);
  var idx := 0;
  while idx < |string_|
    invariant 0 <= idx <= |string_|
    invariant |a| == 30
    invariant |b| == 30
    invariant steps <= 4 * idx + 1
    decreases |string_| - idx
  {
    var q := string_[idx] as int - 'A' as int;
    a := a[q := a[q] + 1];
    idx := idx + 1;
    steps := steps + 4;
  }
  var m := 0;
  var kk := k;
  idx := 0;
  var stopped := false;
  ghost var base2 := steps;
  while idx < |string_| && !stopped
    invariant 0 <= idx <= |string_|
    invariant |a| == 30
    invariant |b| == 30
    invariant steps <= base2 + 8 * idx + (if stopped then 8 else 0)
    decreases !stopped, |string_| - idx
  {
    var q := string_[idx] as int - 'A' as int;
    if a[q] > 0 {
      if b[q] == 0 {
        if kk == 0 {
          m := 1;
          stopped := true;
        } else {
          b := b[q := 1];
          kk := kk - 1;
        }
      }
      if !stopped {
        a := a[q := a[q] - 1];
        if a[q] == 0 {
          kk := kk + 1;
          b := b[q := 1];
        }
      }
    }
    if !stopped {
      idx := idx + 1;
    }
    steps := steps + 8;
  }
  if m == 0 {
    output := "NO";
  } else {
    output := "YES";
  }
  steps := steps + 1;
}
