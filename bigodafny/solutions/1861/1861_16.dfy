// p03222 AtCoder Beginner Contest 113 - Number of Amidakuji  (problem 1861, solution 1861_16)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// f=[0,1,1,2,3,5,8,13,21,34,55,89];h,w,k=map(int,input().split());a=[0]*(w+2);a[1]=1
// for i in range(h):a=[0]+[(f[j-1]*f[w-j+1]*a[j-1]+f[j]*f[w-j+1]*a[j]+f[j]*f[w-j]*a[j+1])%(10**9+7)for j in range(1,w+1)]+[0]
// print(a[k])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
{
  var h := a;
  var w := b;
  var k := c;
  var f := [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89];
  var MOD := 1000000007;
  var arr := seq(w + 2, _ => 0);
  arr := arr[1 := 1];
  var i := 0;
  while i < h
    decreases h - i
  {
    var newArr := seq(w + 2, _ => 0);
    var j := 1;
    while j <= w
      decreases w - j + 1
    {
      var val := (f[j - 1] * f[w - j + 1] * arr[j - 1] + f[j] * f[w - j + 1] * arr[j] + f[j] * f[w - j] * arr[j + 1]) % MOD;
      newArr := newArr[j := val];
      j := j + 1;
    }
    arr := newArr;
    i := i + 1;
  }
  output := IntToString(arr[k]);
}
