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

include "../../../../prelude.dfy"

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires |a_list| == n + 1
  requires n >= 1
  ensures steps <= 2 * NLogN(n) + 20 * n + 30 + 2 * |output|
{
  steps := 0;
  steps := steps + 1;
  var a := a_list[1..];
  SortCostWithin(|a|, n);
  steps := steps + SortCost(|a|);
  var s := SortInts(a);
  var l := 0;
  var r := 0;
  var c := 0;
  var b := 0;
  var i := 1;
  var stop := false;
  while i < n && !stop
    invariant 1 <= i <= n
    invariant 0 <= l <= n
    invariant steps <= 1 + SortCost(|a|) + 11 * (i - 1)
    invariant |a| == n
    invariant 0 <= r <= n
  {
    steps := steps + (3 + if i < n then 1 else 0);
    steps := steps + 4;
    if a[i] < a[i - 1] {
      steps := steps + 1;
      if c == 0 {
        steps := steps + 1;
        l := i - 1;
      }
      c := 1;
    } else {
      steps := steps + 1;
      if c == 1 {
        r := i;
        b := 1;
        stop := true;
      }
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + (2 + if i < n then 1 else 0);
  steps := steps + (2 + if b == 0 then 1 else 0);
  if b == 0 && c == 1 {
    r := n;
  }
  steps := steps + 1;
  if l > r {
    l := r;
  }
  steps := steps + 1;
  var sub := a[l .. r];
  steps := steps + (1 + 5 * |sub|);
  var a1 := seq(|sub|, k requires 0 <= k < |sub| => sub[|sub| - 1 - k]);
  steps := steps + (2 + |a1| + |a[r..]|);
  var newA := a[..l] + a1 + a[r..];
  steps := steps + (2 + if newA == s then 1 else 0);
  if newA == s && c != 0 {
    IntToStringDigits(l + 1);
    IntToStringDigits(r);
    steps := steps + (1 + Digits(l + 1) + |" "| + Digits(r) + |IntToString(r)| + |"\n"|);
    output := IntToString(l + 1) + " " + IntToString(r) + "\n";
  } else {
    output := "0 0\n";
  }
}

import opened Prelude
