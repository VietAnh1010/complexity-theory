// CHARGE SUPERSEDED -- 2026-09-22.
//
//   This proof charges IntToString by the digit count of the printed value.
//   COMPLEXITY.md now charges it 1, and |IntToString(x)| 1 as well. The proof
//   is still SOUND: charging more than the model requires leaves a valid upper
//   bound. It is simply loose, so the row's relation is `looser-slack`, not
//   `looser-structural`, and it left solutions-proved/value-bounded/.
//

include "../../prelude.dfy"
import opened Prelude

function Power(base: int, e: nat): int
  decreases e
{
  if e == 0 then 1 else base * Power(base, e - 1)
}

function HexHelper(s: string): int
  decreases |s|
{
  if |s| == 0 then 1
  else
    var num := (s[0] as int) - ('0' as int);
    if num == 0 then HexHelper(s[1..])
    else if num == 1 then Power(2, |s| - 1) + HexHelper(s[1..])
    else Power(2, |s|)
}

// ---- proof-only cost accounting --------------------------------------
// Both HexHelper and IntToString recurse once per digit of n, so the row's
// real cost is O(digit count of n) == O(log n), not the constant the label
// claims: BigOBench's profiling runs never varied n's digit count.
ghost function HexHelperCost(s: string): nat
  decreases |s|
{
  if |s| == 0 then 1 else 1 + HexHelperCost(s[1..])
}

lemma HexHelperCostBound(s: string)
  ensures HexHelperCost(s) <= |s| + 1
  decreases |s|
{
  if |s| > 0 { HexHelperCostBound(s[1..]); }
}

ghost function IntToStringCost(x: int): nat
  decreases if x < 0 then 1 - x else x
{
  if x < 0 then 1 + IntToStringCost(-x)
  else if x < 10 then 1
  else 1 + IntToStringCost(x / 10)
}

lemma IntToStringCostBound(x: int)
  ensures x >= 0 ==> IntToStringCost(x) <= |IntToString(x)| + 1
  decreases if x < 0 then 1 - x else x
{
  if x < 0 {
  } else if x < 10 {
  } else {
    IntToStringCostBound(x / 10);
  }
}

// Label O(1) -- disagrees. The true cost is linear in the number of digits
// of n, i.e. O(log n): IntToStringCost and HexHelperCost each recurse once
// per digit, and |IntToString(n)| grows with n. No constant bound holds for
// all n.
method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 2 * |IntToString(n)| + 6
{
  var s := IntToString(n);
  IntToStringCostBound(n);
  var result := HexHelper(s) - 1;
  HexHelperCostBound(s);
  steps := IntToStringCost(n) + HexHelperCost(s) + 3;
  output := IntToString(result);
}
