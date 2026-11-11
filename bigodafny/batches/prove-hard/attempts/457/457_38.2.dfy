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

include "../../../../prelude.dfy"

method Solve(n: int, m: int)
    returns (output: string, ghost steps: nat)
  requires n >= 1
  requires 0 <= m <= 9
  ensures steps <= 8 * n * n + 12 * n + 5 + |output|
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
    ghost var it: nat := 0;
    NDOne(nn);
    while NumDigits(nn) != k
      invariant nn >= 1
      invariant pow >= 1
      invariant NumDigits(nn) <= k
      invariant pow <= 8 * nn + 1
      invariant pow == P9(it + 1)
      invariant it <= 2 * k
      invariant steps <= 3 + it * (4 + 4 * k)
      decreases 2 * k - it
    {
      ghost var oldn := nn;
      NDS(nn);
      NDPos(nn);
      steps := steps + (2 + NumDigits_steps(nn));
      steps := steps + 1;
      nn := nn + pow;
      steps := steps + 1;
      pow := pow * 9;
      NDStep(oldn, nn);
      it := it + 1;
      NDLt(nn);
      LogB(it + 1, NumDigits(nn));
      MulStep(it - 1, 4 + 4 * k);
    }
    NDS(nn);
    NDPos(nn);
    MulBound(it, 2 * k, 4 + 4 * k);
    IntToStringDigits(nn);
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

ghost function P9(e: int): nat decreases e { if e <= 0 then 1 else 9 * P9(e - 1) }
ghost function P10(e: int): nat decreases e { if e <= 0 then 1 else 10 * P10(e - 1) }

lemma NDOne(x: int)
  requires 0 <= x < 10
  ensures NumDigits(x) == 1
{}

lemma NDPos(x: int)
  requires x >= 0
  ensures NumDigits(x) >= 1
{}

lemma NDMono(x: int, y: int)
  requires 0 <= x <= y
  ensures NumDigits(x) <= NumDigits(y)
  decreases y
{
  if y >= 10 && x >= 10 { NDMono(x / 10, y / 10); }
  NDPos(y);
}

lemma NDStep(a: int, y: int)
  requires a >= 1 && a <= y <= 10 * a
  ensures NumDigits(y) <= NumDigits(a) + 1
{
  NDMono(y, 10 * a);
  NDPos(a);
  assert (10 * a) / 10 == a;
}

lemma NDLt(x: int)
  requires x >= 0
  ensures x < P10(NumDigits(x))
  decreases x
{
  if x >= 10 { NDLt(x / 10); }
}

lemma NDS(x: int)
  requires x >= 0
  ensures NumDigits_steps(x) <= 4 * NumDigits(x)
  decreases x
{
  if x >= 10 { NDS(x / 10); }
}

lemma P10Pos(e: int)
  ensures P10(e) >= 1
{}

lemma P9Pos(e: int)
  ensures P9(e) >= 1
{}

lemma LogB(i: nat, e: int)
  requires e >= 0
  requires P9(i) <= 8 * P10(e)
  ensures i <= 2 * e + 1
  decreases i
{
  if i >= 2 {
    assert P9(i) == 81 * P9(i - 2);
    P10Pos(e);
    P9Pos(i - 2);
    if e == 0 { assert false; }
    assert P10(e) == 10 * P10(e - 1);
    LogB(i - 2, e - 1);
  }
}

lemma MulStep(i: nat, c: nat)
  ensures (i + 1) * c == i * c + c
{}

lemma MulBound(a: nat, b: nat, c: nat)
  requires a <= b
  ensures a * c <= b * c
{}

import opened Prelude
