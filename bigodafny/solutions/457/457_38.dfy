// 355_A. Vasya and Digital Root  (problem 457, solution 457_38)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
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
import opened Prelude

method Solve(n: int, m: int) returns (output: string)
  requires n >= 1
  requires 0 <= m <= 9
{
  var k := n;
  var d := m;
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
      decreases P10(k) - nn
    {
      NumDigitsLt(nn, k);
      if i >= 2 * k { Pow9Ge(i, k); }
      NumDigitsGrow(nn, nn + pow);
      NumDigitsPos(nn + pow);
      NumDigitsLt(nn + pow, k);
      nn := nn + pow;
      pow := pow * 9;
      i := i + 1;
    }
    output := IntToString(nn) + "\n";
  }
}

function NumDigits(x: int): int
  requires x >= 0
  decreases x
{
  if x < 10 then 1 else 1 + NumDigits(x / 10)
}

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
