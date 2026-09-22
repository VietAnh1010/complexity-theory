// VALUE-BOUNDED -- filed for review; the proof carries a term the label omits.
//
//   This proof's bound depends on the MAGNITUDE of an input, not only on how
//   many inputs there are. BigOBench fitted the label by profiling, which
//   treats a capped value as constant; COMPLEXITY.md section 1 decides the
//   opposite, so the two disagree here by construction.
//
//   See solutions-proved/value-bounded/README.md for the category and
//   MANIFEST.jsonl for this row's entry.
//
// 9_C. Hexadecimal's Numbers  (problem 2381, solution 2381_156)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
// 	n = int(input())
// 	print(calculate(n))
//
// def helper(s):
// 	if len(s) == 0:
// 		return 1
// 	num = int(s[0])
// 	if num == 0:
// 		return helper(s[1:])
// 	elif num == 1:
// 		return 2**(len(s) - 1) + helper(s[1:])
// 	elif num >= 2:
// 		return 2**len(s)
// 	else:
// 		assert(False)
//
// def calculate(n):
// 	return helper(str(n)) - 1
//
// main()
// #print(calculate(13402))
// --------------------------------------------------------------------

include "../../../prelude.dfy"
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
