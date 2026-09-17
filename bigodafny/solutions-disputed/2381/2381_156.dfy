// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : O(log n)
//   cause          : label
//   confidence     : high
//   auditor        : value-vs-size convention, 2026-09-17
//
//   The label disagrees with the code under the value-versus-size
//   convention. BigOBench fitted its labels by profiling, which treats a
//   capped input value as constant; COMPLEXITY.md section 1 decides the
//   opposite. This row is where the two disagree.
//
//   evidence:
//     This is the exact case the 2026-09-17 convention rejects.
//     IntToString and HexHelper cost the digit count of n, which is log
//     of the value. The label calls that constant. It is bounded, so
//     O(1) is formally defensible, but the hidden constant is the full
//     64-bit digit loop and the label then predicts nothing about
//     growth.
//
//   how this label could be wrong, and what to check:
//     Confirm the only n-dependent work is digit production. If so the
//     row is O(log n) and the O(1) label is a convention disagreement,
//     not a translation defect -- the translation is faithful.
//
//   note: the translation is NOT at fault in any of these four rows. The
//   proof in solutions-proved/ is correct and stays there.
// --------------------------------------------------------------------

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
