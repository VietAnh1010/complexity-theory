// LABEL AUDIT WITHDRAWN -- 2026-09-22.
//
//   This row was moved to solutions-disputed/ because its proof charged
//   IntToString by the digit count of the printed value, which made the cost
//   grow with the value's magnitude while the label counted only how many
//   items there were. That charge was the ENTIRE basis for the move.
//
//   COMPLEXITY.md now charges IntToString 1, and treats |IntToString(x)| as 1
//   as well so Join cannot reintroduce the digit count. Under that model this
//   row's label omits nothing, so the dispute does not exist and the row is
//   back in solutions/.
//
//   The proof in solutions-proved/ still carries the old digit term. That is
//   sound -- it charges MORE than the model requires, so it remains a valid
//   upper bound -- but it is now loose rather than structural, and it is
//   recorded as `looser-slack`. A tight re-proof is available work.
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

method Solve(n: int) returns (output: string)
{
  var s := IntToString(n);
  var result := HexHelper(s) - 1;
  output := IntToString(result);
}
