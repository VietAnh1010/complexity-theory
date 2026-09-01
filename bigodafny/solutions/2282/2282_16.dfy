// 489_C. Given Length and Sum of Digits...  (problem 2282, solution 2282_16)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=input().split()
// n[0]=int(n[0])
// n[1]=int(n[1])
// if n[1]==0:
//     if n[0]==1:
//         print('0 0')
//     if n[0]!=1:
//         print('-1 -1')
// elif n[0]*9<n[1]:
//     print('-1 -1')
// else:
//     i=(n[1]-1)//9
//     q=(n[1]-1)%9
//     mi=10**(n[0]-1)+q*10**i
//     while i>0:
//         mi+=9*10**(i-1)
//         i=i-1
//     ii=n[1]//9
//     qq=n[1]%9
//     if qq==0:
//         ma=ii*'9'+(n[0]-ii)*'0'
//     else:
//         ma=ii*'9'+str(qq)+'0'*(n[0]-ii-1)
//     print(mi,ma)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int) returns (output: string)
{
  var n0 := n;
  var n1 := k;
  if n1 == 0 {
    if n0 == 1 {
      output := "0 0";
    } else {
      output := "-1 -1";
    }
  } else if n0 * 9 < n1 {
    output := "-1 -1";
  } else {
    var i := (n1 - 1) / 9;
    var q := (n1 - 1) % 9;
    var mi := Pow10_2282(n0 - 1) + q * Pow10_2282(i);
    var ii2 := i;
    while ii2 > 0
      decreases ii2
    {
      mi := mi + 9 * Pow10_2282(ii2 - 1);
      ii2 := ii2 - 1;
    }
    var ii := n1 / 9;
    var qq := n1 % 9;
    var ma: string;
    if qq == 0 {
      ma := Repeat("9", ii) + Repeat("0", n0 - ii);
    } else {
      ma := Repeat("9", ii) + IntToString(qq) + Repeat("0", n0 - ii - 1);
    }
    output := IntToString(mi) + " " + ma;
  }
}

function Pow10_2282(e: int): int
  decreases if e > 0 then e else 0
{
  if e <= 0 then 1 else 10 * Pow10_2282(e - 1)
}
