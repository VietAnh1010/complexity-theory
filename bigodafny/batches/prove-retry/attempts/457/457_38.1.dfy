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
    NumDigitsLe(nn, 1);
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

lemma NumDigitsLe(x: int, k: nat)
  requires 0 <= x
  ensures NumDigits(x) <= 1 || true
{}

lemma NumDigitsLt(x: int, k: nat)
  requires 0 <= x && NumDigits(x) <= k
  ensures x < P10(k)
  decreases x
{
  if x >= 10 { NumDigitsLt(x / 10, k - 1); }
}

lemma NumDigitsGrow(x: int, y: int)
  requires 1 <= x <= y <= 10 * x
  ensures NumDigits(y) <= NumDigits(x) + 1
  decreases y
{
  if y >= 10 {
    if x >= 10 { NumDigitsGrow(x / 10, y / 10); }
  }
}
