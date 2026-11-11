// --- Python ---------------------------------------------------------
// a = "abcdefghijklmnopqrstuvwxyz"
// def alpha (r,n):
//     if len(r)==1 and r[0]==n:
//         print("YES")
//         return 0
//     elif r[0]==n:
//         alpha(r[1:],a[(a.find(n))-1])
//     elif r[-1]==n:
//          alpha(r[:-1],a[(a.find(n))-1])
//     else:
//         print("NO")
// k = int(input())
// for i in range(k):
//     r = str(input())
//     alpha(r,a[len(r)-1])
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(strings: seq<string>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |strings| ==> 1 <= |strings[k]| <= 26
  ensures steps <= 300 * |strings| + 2
{
  steps := 0;
  var results: seq<string> := [];
  var si := 0;
  while si < |strings|
    invariant 0 <= si <= |strings|
    invariant steps <= 296 * si
    invariant |results| == si
    invariant SumLen(results) <= 3 * si
    decreases |strings| - si
  {
    ghost var t0 := steps;
    steps := steps + 3;
    steps := steps + 1;
    var r := strings[si];
    steps := steps + 2;
    var idxLetter := |r| - 1;
    var res := "";
    var done := false;
    ghost var s0 := steps;
    assert s0 == t0 + 6;
    while !done
      invariant |res| <= 3
      invariant steps <= s0 + 11 * (26 - |r|) + (if done then 9 else 0)
      invariant 1 <= |r| <= 26
      invariant idxLetter == |r| - 1
      decreases !done, |r|
    {
      steps := steps + 2;
      steps := steps + 3;
      var n := ('a' as int + idxLetter) as char;
      steps := steps + 2;
      if |r| == 1 {
        steps := steps + 2;
        if r[0] == n {
          res := "YES";
        } else {
          res := "NO";
        }
        done := true;
      } else if r[0] == n {
        steps := steps + 1;
        r := r[1..];
        steps := steps + 1;
        idxLetter := idxLetter - 1;
      } else if r[|r| - 1] == n {
        steps := steps + 3;
        r := r[..|r| - 1];
        steps := steps + 1;
        idxLetter := idxLetter - 1;
      } else {
        res := "NO";
        done := true;
      }
    }
    steps := steps + 1;
    steps := steps + (1 + |[res]|);
    SumLenSnoc(results, res);
    results := results + [res];
    steps := steps + 1;
    si := si + 1;
  }
  steps := steps + 2;
  steps := steps + (SumLen(results) + |results|);
  output := Join(results, "\n");
}

import opened Prelude
