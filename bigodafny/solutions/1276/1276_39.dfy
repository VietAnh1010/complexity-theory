// p02992 AtCoder Beginner Contest 132 - Small Products  (problem 1276, solution 1276_39)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// mod=1000000007
// n,k=map(int,input().split())
// s=int(n**0.5)
// Num=[0]*(s+1)
// for i in range(s,0,-1):
//     Num[i]=i
//     Num.append(n//i)
// l=len(Num)
// for i in range(1,l):
//     Num[-i]=Num[-i]-Num[-i-1]
// DP=[[0]*l for _ in range(k)]
// DP[0]=Num[:]
// for i in range(1,k):
//     tmp=0
//     for j in range(1,l):
//         tmp+=DP[i-1][j]
//         tmp%=mod
//         DP[i][-j]=(tmp*Num[-j])%mod
// ans=0
// for i in DP[-1][1:]:
//     ans+=i
//     ans%=mod
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
{

  var n := a;
  var k := b;
  var mod := 1000000007;
  var s := 0;
  while (s+1)*(s+1) <= n
    decreases n - s*s
  {
    s := s + 1;
  }
  var l := 2*s + 1;
  var num0 := new int[l];
  var ii := 0;
  while ii <= s
    decreases s - ii
  {
    num0[ii] := ii;
    ii := ii + 1;
  }
  var tt := 0;
  while tt < s
    decreases s - tt
  {
    num0[s+1+tt] := n / (s - tt);
    tt := tt + 1;
  }
  var num := new int[l];
  num[0] := num0[0];
  var jj := 1;
  while jj < l
    decreases l - jj
  {
    num[jj] := num0[jj] - num0[jj-1];
    jj := jj + 1;
  }

  var prevRow := num;
  var i := 1;
  while i < k
    decreases k - i
  {
    var row := new int[l];
    var tmp := 0;
    var j := 1;
    while j < l
      decreases l - j
    {
      tmp := (tmp + prevRow[j]) % mod;
      row[l - j] := (tmp * num[l - j]) % mod;
      j := j + 1;
    }
    prevRow := row;
    i := i + 1;
  }

  var ans := 0;
  var idx := 1;
  while idx < l
    decreases l - idx
  {
    ans := (ans + prevRow[idx]) % mod;
    idx := idx + 1;
  }
  output := IntToString(ans);
}
}
