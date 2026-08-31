// 110_C. Lucky Sum of Digits  (problem 271, solution 271_58)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// aux = 0
// if n < 4:
// 	print('-1')
// else:
// 	numSeven = n/7
// 	rem = n%7
// 	numFour = rem/4
// 	toBecomeFour = rem%4
// 	if toBecomeFour != 0:
// 		if numSeven >= toBecomeFour:
// 			numFour += ((7*toBecomeFour) + toBecomeFour)/4
// 			numSeven -= toBecomeFour
// 		else:
// 			print("-1")
// 			aux = 1
// 
// 	if aux == 0:
// 		for i in range(int(numFour)):
// 			print("4",end='')
// 		for i in range(int(numSeven)):
// 			print("7", end='')
// 		print("")
// 		  	 	 	 		 		      	 		  		
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  if n < 4 {
    output := "-1";
  } else {
    var numSeven := n / 7;
    var rem := n % 7;
    var toBecomeFour := rem % 4;
    var numFour := rem / 4;
    var aux := 0;
    if toBecomeFour != 0 {
      if numSeven >= toBecomeFour {
        numFour := rem / 4 + 2 * toBecomeFour;
        numSeven := numSeven - toBecomeFour;
      } else {
        aux := 1;
      }
    }
    if aux == 0 {
      output := Repeat('4', numFour) + Repeat('7', numSeven);
    } else {
      output := "-1";
    }
  }
}

function Repeat(c: char, n: int): string
  decreases if n < 0 then 0 else n
{
  if n <= 0 then "" else [c] + Repeat(c, n - 1)
}
