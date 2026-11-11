// --- Python ---------------------------------------------------------
// f=[0,1,1,2,3,5,8,13,21,34,55,89];h,w,k=map(int,input().split());a=[0]*(w+2);a[1]=1
// for i in range(h):a=[0]+[(f[j-1]*f[w-j+1]*a[j-1]+f[j]*f[w-j+1]*a[j]+f[j]*f[w-j]*a[j+1])%(10**9+7)for j in range(1,w+1)]+[0]
// print(a[k])
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(a: int, b: int, c: int)
    returns (output: string, ghost steps: nat)
  requires a >= 1
  requires 1 <= b <= 11
  requires 0 <= c <= b + 1
  ensures steps <= 348 * a + 29 + |output|
{
  steps := 0;
  var h := a;
  var w := b;
  var k := c;
  steps := steps + 12;
  var f := [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89];
  var MOD := 1000000007;
  steps := steps + (1 + (w + 2));
  var arr := seq(w + 2, _ /* _v0 */ => 0);
  steps := steps + 1;
  arr := arr[1 := 1];
  var i := 0;
  while i < h
    invariant |arr| == w + 2
    invariant 0 <= i <= h
    invariant steps <= w + 16 + i * 348
    decreases h - i
  {
    steps := steps + 2;
    steps := steps + (1 + (w + 2));
    var newArr := seq(w + 2, _ /* _v1 */ => 0);
    var j := 1;
    ghost var s0 := steps;
    while j <= w
      invariant 1 <= j <= w + 1
      invariant |newArr| == w + 2
      invariant steps <= s0 + (j - 1) * 30
      decreases w - j + 1
    {
      steps := steps + 2;
      steps := steps + 26;
      var val := (f[j - 1] * f[w - j + 1] * arr[j - 1] + f[j] * f[w - j + 1] * arr[j] + f[j] * f[w - j] * arr[j + 1]) % MOD;
      steps := steps + 1;
      newArr := newArr[j := val];
      steps := steps + 1;
      j := j + 1;
    }
    steps := steps + 1;
    arr := newArr;
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  steps := steps + (1 + Digits(arr[k]));
  output := IntToString(arr[k]);
  IntToStringDigits(arr[k]);
}

import opened Prelude
