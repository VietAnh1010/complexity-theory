// 1_B. Spreadsheets  (problem 1047, solution 1047_641)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import re
// 
// for t in range(int(input())):
// 	a = input()
// 
// 	if re.search("R\d+C\d+",a):
// 		row,col= a.split("C")
// 		row = row[1:]
// 		col = int(col)
// 
// 		ans = ""
// 
// 		while col:
// 			temp = col%26+64
// 			if temp == 64:
// 				temp = 90
// 				col-=1
// 			ans = chr(temp) + ans
// 			col//=26
// 		print(ans+row)
// 	else:
// 
// 		col = ""
// 
// 		for i in a:
// 			if i.isalpha():
// 				col+=i
// 			else:
// 				break
// 
// 		row = a.replace(col,"")
// 
// 		ans = 0
// 
// 
// 		for i in col:
// 			ans = 26*ans + (ord(i)-64)
// 
// 		print("R"+row+"C"+str(ans))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
