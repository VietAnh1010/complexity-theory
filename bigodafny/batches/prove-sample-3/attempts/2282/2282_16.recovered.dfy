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

function Pow10_2282(e: int): int
  decreases if e > 0 then e else 0
{
  if e <= 0 then 1 else 10 * Pow10_2282(e - 1)
}

// Pow10_2282 recurses e times: each call to it costs its argument, not O(1).
// The while loop below calls it once per iteration with an argument that
// shrinks by 1 each time, so the loop's real cost is a shrinking series,
// quadratic in i -- the hidden n**2 the label names.
ghost function Pow10Steps(e: int): nat
  decreases if e > 0 then e else 0
{ if e <= 0 then 1 else 1 + Pow10Steps(e - 1) }

lemma Pow10StepsVal(e: int)
  ensures Pow10Steps(e) == (if e > 0 then e else 0) + 1
  decreases if e > 0 then e else 0
{
  if e <= 0 {
  } else {
    Pow10StepsVal(e - 1);
  }
}

// Isolated multiplication: bumping the progress count by 1 adds exactly c.
lemma DistribStep(a: int, c: int)
  ensures (a + 1) * c == a * c + c
{}

// Isolated multiplication: i*(i+5) is monotone in i over the naturals.
lemma MulMonoQuad(i: int, n: int)
  requires 0 <= i <= n
  ensures i * (i + 5) <= n * (n + 5)
{}

method Solve(n: int, k: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires k >= 0
  ensures steps <= (n + 5) * n + 40
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
    steps := steps + 2;
  } else if n0 * 9 < n1 {
    output := "-1 -1";
    steps := steps + 2;
  } else {
    var i := (n1 - 1) / 9;
    var q := (n1 - 1) % 9;
    Pow10StepsVal(n0 - 1);
    Pow10StepsVal(i);
    var mi := Pow10_2282(n0 - 1) + q * Pow10_2282(i);
    steps := steps + Pow10Steps(n0 - 1) + Pow10Steps(i) + 4;
    // n0*9 >= n1 (else branch above excludes n0*9 < n1), so i == (n1-1)/9 < n0.
    assert 9 * n0 >= n1;
    assert i < n0;
    var ii2 := i;
    ghost var base1 := steps;
    while ii2 > 0
      invariant 0 <= ii2 <= i
      invariant steps <= base1 + (i - ii2) * (i + 5)
      decreases ii2
    {
      Pow10StepsVal(ii2 - 1);
      assert Pow10Steps(ii2 - 1) == ii2;
      assert ii2 <= i;
      DistribStep(i - ii2, i + 5);
      mi := mi + 9 * Pow10_2282(ii2 - 1);
      steps := steps + Pow10Steps(ii2 - 1) + 3;
      ii2 := ii2 - 1;
    }
    MulMonoQuad(i, n0);
    var ii := n1 / 9;
    var qq := n1 % 9;
    var ma: string;
    assert 9 * ii + qq == n1;
    assert 9 * n0 >= n1;
    steps := steps + 4;
    if qq == 0 {
      ma := Repeat("9", ii) + Repeat("0", n0 - ii);
      steps := steps + (n0 - ii) + ii + 2;
    } else {
      ma := Repeat("9", ii) + IntToString(qq) + Repeat("0", n0 - ii - 1);
      steps := steps + (n0 - ii - 1) + ii + 3;
    }
    output := IntToString(mi) + " " + ma;
    steps := steps + 2;
  }
}
