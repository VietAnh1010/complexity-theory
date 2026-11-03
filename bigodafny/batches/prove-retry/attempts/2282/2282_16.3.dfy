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

include "../../../../prelude.dfy"

lemma PowSteps2282(e: int)
  ensures Pow10_2282_steps(e) == 4 * (if e > 0 then e else 0) + 2
  decreases if e > 0 then e else 0
{
  if e > 0 { PowSteps2282(e - 1); }
}

lemma RepLen2282(c: string, k: nat)
  requires |c| == 1
  ensures |Repeat(c, k)| == k
{
}

method Solve(n: int, k: int)
    returns (output: string, ghost steps: nat)
  requires n >= 0
  requires k >= 0
  ensures steps <= n * (4 * n + 4) + 10 * n + 16 + |output|
{
  steps := 0;
  var n0 := n;
  var n1 := k;
  steps := steps + 1;
  if n1 == 0 {
    steps := steps + 1;
    if n0 == 1 {
      output := "0 0";
    } else {
      output := "-1 -1";
    }
  } else if n0 * 9 < n1 {
    output := "-1 -1";
  } else {
    steps := steps + 2;
    var i := (n1 - 1) / 9;
    steps := steps + 2;
    var q := (n1 - 1) % 9;
    assert 0 <= i <= n0;
    PowSteps2282(n0 - 1);
    PowSteps2282(i);
    steps := steps + (3 + Pow10_2282_steps(n0 - 1) + Pow10_2282_steps(i));
    var mi := Pow10_2282(n0 - 1) + q * Pow10_2282(i);
    var ii2 := i;
    ghost var b := steps;
    ghost var K: nat := 4 * n0 + 4;
    while ii2 > 0
      invariant 0 <= ii2 <= i
      invariant steps <= b + (i - ii2) * K
      decreases ii2
    {
      PowSteps2282(ii2 - 1);
      CostMulDistrib(i - ii2, 1, i - ii2 + 1, K);
      steps := steps + 2;
      steps := steps + (3 + Pow10_2282_steps(ii2 - 1));
      mi := mi + 9 * Pow10_2282(ii2 - 1);
      steps := steps + 1;
      ii2 := ii2 - 1;
    }
    CostMulMonoLeft(i, n0, K);
    steps := steps + 1;
    steps := steps + 1;
    var ii := n1 / 9;
    steps := steps + 1;
    var qq := n1 % 9;
    var ma: string;
    assert 9 * ii + qq == n1;
    assert 9 * n0 >= n1;
    steps := steps + 1;
    if qq == 0 {
      RepLen2282("9", ii);
      RepLen2282("0", n0 - ii);
      steps := steps + (1 + |"9"| * ii + |"0"| * (n0 - ii) + |Repeat("0", n0 - ii)|);
      ma := Repeat("9", ii) + Repeat("0", n0 - ii);
    } else {
      RepLen2282("9", ii);
      RepLen2282("0", n0 - ii - 1);
      IntToStringDigits(qq);
      steps := steps + (2 + |"9"| * ii + Digits(qq) + |IntToString(qq)| + |"0"| * (n0 - ii - 1) + |Repeat("0", n0 - ii - 1)|);
      ma := Repeat("9", ii) + IntToString(qq) + Repeat("0", n0 - ii - 1);
    }
    IntToStringDigits(mi);
    steps := steps + (Digits(mi) + |" "| + |ma|);
    output := IntToString(mi) + " " + ma;
  }
}

function Pow10_2282(e: int): int
  decreases if e > 0 then e else 0
{
  if e <= 0 then
    1
  else
    10 * Pow10_2282(e - 1)
}

ghost function Pow10_2282_steps(e: int): nat
  decreases if e > 0 then e else 0
{
  2 + if e <= 0 then 0 else 2 + Pow10_2282_steps(e - 1)
}

import opened Prelude
