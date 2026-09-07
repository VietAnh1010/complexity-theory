// 56_B. Spoilt Permutation  (problem 2771, solution 2771_23)
// time complexity: O(nlogn)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// s=sorted(a)
// l=0
// r=0
// c=0
// b=0
// for i in range(1,n):
//     if a[i]<a[i-1]:
//         l=i-1 if c==0 else l
//         c=1
//     else:
//         if c==1:
//             r=i
//             b=1
//             break
// if b==0 and c==1:
//     r=n
// a1=a[l:r]
// a1.reverse()
// a=a[:l]+a1+a[r:]
// if a==s and c:
//     print(l+1,r)
// else:
//     print(0,0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| == n + 1
  requires n >= 0
{
  var a := a_list[1..];
  var s := SortInts(a);
  var l := 0;
  var r := 0;
  var c := 0;
  var b := 0;
  var i := 1;
  var stop := false;
  while i < n && !stop
    invariant 0 <= i
    invariant 0 <= l
    invariant 0 <= r <= n
  {
    if a[i] < a[i - 1] {
      if c == 0 { l := i - 1; }
      c := 1;
    } else {
      if c == 1 {
        r := i;
        b := 1;
        stop := true;
      }
    }
    i := i + 1;
  }
  if b == 0 && c == 1 {
    r := n;
  }
  if l > r { l := r; }
  var sub := a[l..r];
  var a1 := seq(|sub|, k requires 0 <= k < |sub| => sub[|sub| - 1 - k]);
  var newA := a[..l] + a1 + a[r..];
  if newA == s && c != 0 {
    output := IntToString(l + 1) + " " + IntToString(r) + "\n";
  } else {
    output := "0 0\n";
  }
}
