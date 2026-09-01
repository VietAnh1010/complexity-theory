// 1436_C. Binary Search  (problem 1359, solution 1359_189)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x,a = map(int,input().split())
// ans = 1
// cnt = 0
// cnt1 = 0
// i = 0
// j = n
// mod = 1000000007
// while i<j:
// 	mid = (i+j)//2
// 	if mid<a:
// 		ans*=(x-1-cnt1)
// 		ans%=mod
// 		cnt1+=1
// 		i = mid+1
// 	elif mid>a:
// 		ans*=(n-x-cnt)
// 		ans%=mod
// 		cnt+=1
// 		j = mid
// 	else:
// 		i = mid+1
// cr = n-cnt-cnt1-1
// for i in range(1,cr+1):
// 	ans*=i
// 	ans%=mod
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
{
{

  var n := a;
  var x := b;
  var target := c;
  var mod := 1000000007;
  var ans := 1;
  var cnt := 0;
  var cnt1 := 0;
  var i := 0;
  var j := n;
  while i < j
    decreases j - i
  {
    var mid := (i + j) / 2;
    if mid < target {
      ans := (ans * (x - 1 - cnt1)) % mod;
      cnt1 := cnt1 + 1;
      i := mid + 1;
    } else if mid > target {
      ans := (ans * (n - x - cnt)) % mod;
      cnt := cnt + 1;
      j := mid;
    } else {
      i := mid + 1;
    }
  }
  var cr := n - cnt - cnt1 - 1;
  var k := 1;
  while k <= cr
    decreases cr - k
  {
    ans := (ans * k) % mod;
    k := k + 1;
  }
  output := IntToString(ans);
}
}
