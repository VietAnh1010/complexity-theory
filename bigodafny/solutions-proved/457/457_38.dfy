// --- Python ---------------------------------------------------------
// l=input().split()
// k=int(l[0])
// d=int(l[1])
// if(k==1 and d==0):
// 	print(0)
// elif(k!=1 and d==0):
// 	print('No solution')
// else:
// 	i=1
// 	n=d
// 	while len(str(n))!=k:
// 		n+=9**(i)
// 		i+=1
// 	print(n)
// --------------------------------------------------------------------

include "../../prelude.dfy"

method Solve(n: int, m: int)
    returns (output: string, ghost steps: nat)
  requires n >= 1
  requires 0 <= m <= 9
  ensures steps <= 8 * n * n + 12 * n + 4 + |output|
{
  steps := 0;
  var k := n;
  var d := m;
  steps := steps + (2 + if k == 1 then 1 else 0);
  if k == 1 && d == 0 {
    output := "0\n";
  } else if k != 1 && d == 0 {
    output := "No solution\n";
  } else {
    var nn := d;
    var pow := 9;
    ghost var i: nat := 0;
    NumDigitsPos(nn);
    while NumDigits(nn) != k
      invariant nn >= 0
      invariant pow >= 1
      invariant nn >= 1
      invariant pow == Pow9(i + 1)
      invariant nn >= Pow9(i)
      invariant NumDigits(nn) <= k
      invariant i <= 2 * k
      invariant steps <= 3 + i * (4 * k + 4)
      decreases P10(k) - nn
    {
      NumDigitsLt(nn, k);
      if i >= 2 * k { Pow9Ge(i, k); }
      NDSEq(nn);
      NumDigitsGrow(nn, nn + pow);
      NumDigitsPos(nn + pow);
      NumDigitsLt(nn + pow, k);
      CostMulDistrib(i, 1, i + 1, 4 * k + 4);
      steps := steps + (2 + NumDigits_steps(nn));
      steps := steps + 1;
      nn := nn + pow;
      steps := steps + 1;
      pow := pow * 9;
      i := i + 1;
    }
    NDSEq(nn);
    DigitsEq(nn);
    IntToStringDigits(nn);
    CostMulMonoLeft(i, 2 * k, 4 * k + 4);
    steps := steps + (1 + NumDigits_steps(nn));
    steps := steps + (Digits(nn) + |"\n"|);
    output := IntToString(nn) + "\n";
  }
}

function NumDigits(x: int): int
  requires x >= 0
  decreases x
{
  if x < 10 then
    1
  else
    1 + NumDigits(x / 10)
}

ghost function NumDigits_steps(x: int): nat
  requires x >= 0
  decreases x
{
  2 + if x < 10 then 0 else 2 + NumDigits_steps(x / 10)
}

import opened Prelude

ghost function P10(k: nat): nat { if k == 0 then 1 else 10 * P10(k - 1) }

ghost function Pow9(i: nat): nat { if i == 0 then 1 else 9 * Pow9(i - 1) }

lemma P10Pos(k: nat)
  ensures P10(k) >= 1
{
  if k > 0 { P10Pos(k - 1); }
}

lemma Pow9Pos(i: nat)
  ensures Pow9(i) >= 1
{
  if i > 0 { Pow9Pos(i - 1); }
}

lemma Pow9Ge(i: nat, k: nat)
  requires i >= 2 * k
  ensures Pow9(i) >= P10(k)
{
  if k == 0 { Pow9Pos(i); } else { Pow9Ge(i - 2, k - 1); }
}

lemma NumDigitsPos(x: int)
  requires 0 <= x
  ensures NumDigits(x) >= 1
{
  if x >= 10 { NumDigitsPos(x / 10); }
}

lemma NDSEq(x: int)
  requires x >= 0
  ensures NumDigits_steps(x) + 2 == 4 * NumDigits(x)
{
  if x >= 10 { NDSEq(x / 10); }
}

lemma DigitsEq(x: int)
  requires x >= 0
  ensures Digits(x) == NumDigits(x)
{
  if x >= 10 { DigitsEq(x / 10); }
}

lemma NumDigitsLt(x: int, k: nat)
  requires 0 <= x && NumDigits(x) <= k
  ensures x < P10(k)
  decreases x
{
  NumDigitsPos(x);
  P10Pos(k);
  if x >= 10 { NumDigitsLt(x / 10, k - 1); }
}

lemma NumDigitsMono(x: int, y: int)
  requires 0 <= x <= y
  ensures NumDigits(x) <= NumDigits(y)
  decreases y
{
  if x >= 10 { NumDigitsMono(x / 10, y / 10); }
}

lemma NumDigitsGrow(x: int, y: int)
  requires 1 <= x <= y <= 10 * x
  ensures NumDigits(y) <= NumDigits(x) + 1
{
  NumDigitsMono(y, 10 * x);
  assert NumDigits(10 * x) == 1 + NumDigits(x);
}
