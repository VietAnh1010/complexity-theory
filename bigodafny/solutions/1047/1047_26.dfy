// 1_B. Spreadsheets  (problem 1047, solution 1047_26)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import re
// 
// 
// f = lambda n: sum((ord(k)-64) * 26**i for i, k in enumerate(str(n)[::-1]))
// 
// g = lambda n: '' if not n else (g(n // 26) + chr(n % 26 + 64) if n % 26 else g(n // 26 - 1) + 'Z')
// 
// for cell in [input() for i in range(int(input()))]:
// 	if re.search('R\d+C\d+', cell):
// 		print(g(int(cell[cell.find('C')+1:])) + cell[1:cell.find('C')])
// 	else:
// 		first_digit_index = re.search('\d', cell).start()
// 		print('R' + cell[first_digit_index:] + 'C' + str(f(cell[:first_digit_index])))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
