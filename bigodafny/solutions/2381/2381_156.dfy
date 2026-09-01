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
