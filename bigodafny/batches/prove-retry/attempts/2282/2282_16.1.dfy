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

ghost function Pow10Steps(e: int): nat
  decreases if e > 0 then e else 0
{ if e <= 0 then 1 else Pow10Steps(e - 1) + 2 }

lemma Pow10StepsBound(e: int)
  ensures Pow10Steps(e) <= 2 * (if e > 0 then e else 0) + 1
  decreases if e > 0 then e else 0
{
  if e > 0 { Pow10StepsBound(e - 1); }
}

lemma RepLen(c: string, k: nat)
  requires |c| == 1
  ensures |Repeat(c, k)| == k
{
}

method Solve(n: int, k: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires k >= 0
  ensures steps <= n * (2 * n + 6) + 6 * n + 3 * |output| + 30
{
  steps := 1;
  var n0 := n;
  var n1 := k;
  if n1 == 0 {
    if n0 == 1 {
      output := "0 0";
    } else {
      output := "-1 -1";
    }
    steps := steps + 3 + |output|;
  } else if n0 * 9 < n1 {
    output := "-1 -1";
    steps := steps + 4 + |output|;
  } else {
    var i := (n1 - 1) / 9;
    var q := (n1 - 1) % 9;
    assert i <= n0;
    steps := steps + 6;
    Pow10StepsBound(n0 - 1);
    Pow10StepsBound(i);
    var mi := Pow10_2282(n0 - 1) + q * Pow10_2282(i);
    steps := steps + Pow10Steps(n0 - 1) + Pow10Steps(i) + 3;
    var ii2 := i;
    ghost var b := steps;
    ghost var K := 2 * n0 + 8;
    while ii2 > 0
      invariant 0 <= ii2 <= i
      invariant steps <= b + (i - ii2) * K
      decreases ii2
    {
      Pow10StepsBound(ii2 - 1);
      mi := mi + 9 * Pow10_2282(ii2 - 1);
      steps := steps + Pow10Steps(ii2 - 1) + 6;
      CostMulDistrib(i - ii2, 1, i - ii2 + 1, K);
      ii2 := ii2 - 1;
    }
    CostMulMonoLeft(i, n0, K);
    CostMulDistrib(n0, 0, n0, 0);
    var ii := n1 / 9;
    var qq := n1 % 9;
    var ma: string;
    assert 9 * ii + qq == n1;
    assert 9 * n0 >= n1;
    steps := steps + 4;
    if qq == 0 {
      RepLen("9", ii);
      RepLen("0", n0 - ii);
      ma := Repeat("9", ii) + Repeat("0", n0 - ii);
      steps := steps + ii + (n0 - ii) + |ma|;
    } else {
      RepLen("9", ii);
      RepLen("0", n0 - ii - 1);
      IntToStringDigits(qq);
      ma := Repeat("9", ii) + IntToString(qq) + Repeat("0", n0 - ii - 1);
      steps := steps + ii + (n0 - ii) + Digits(qq) + |ma| + 2;
    }
    IntToStringDigits(mi);
    output := IntToString(mi) + " " + ma;
    steps := steps + Digits(mi) + |output|;
    CostMulMono(n0, 2 * n0 + 6, K);
  }
}

function Pow10_2282(e: int): int
  decreases if e > 0 then e else 0
{
  if e <= 0 then 1 else 10 * Pow10_2282(e - 1)
}
