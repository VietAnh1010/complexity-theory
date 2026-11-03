include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int) returns (output: string, ghost steps: nat)
  requires n >= 1
  requires 0 <= m <= 9
{
  steps := 1;
  var k := n;
  var d := m;
  if k == 1 && d == 0 {
    output := "0\n";
  } else if k != 1 && d == 0 {
    output := "No solution\n";
  } else {
    var nn := d;
    var pow := 9;
    while NumDigits(nn) != k
      invariant nn >= 1
      invariant pow >= 1
      invariant pow <= 9 * nn
      invariant NumDigits(nn) <= k
      decreases P10(k) - nn
    {
      NumDigitsGrow(nn, nn + pow);
      NumDigitsLt(nn + pow, k);
      NumDigitsLt(nn, k);
      nn := nn + pow;
      pow := pow * 9;
      steps := steps + 1;
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

lemma P10Pos(k: nat)
  ensures P10(k) >= 1
{
  if k > 0 { P10Pos(k - 1); }
}

lemma NumDigitsLe(x: int, k: nat)
  requires 0 <= x
  ensures NumDigits(x) >= 1
  decreases x
{
  if x >= 10 { NumDigitsLe(x / 10, k); }
}

lemma NumDigitsLt(x: int, k: nat)
  requires 0 <= x && NumDigits(x) <= k
  ensures x < P10(k)
  decreases x
{
  NumDigitsLe(x, k);
  P10Pos(k);
  if x >= 10 {
    NumDigitsLe(x / 10, k);
    assert k >= 1;
    P10Pos(k - 1);
    NumDigitsLt(x / 10, k - 1);
  } else {
    assert k >= 1;
    P10Pos(k - 1);
  }
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
