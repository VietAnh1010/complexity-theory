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

include "../../../../prelude.dfy"

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= n + 25
{
  steps := 0;
  steps := steps + 1;
  if n < 4 {
    output := "-1";
  } else {
    steps := steps + 1;
    var numSeven := n / 7;
    steps := steps + 1;
    var rem := n % 7;
    steps := steps + 1;
    var toBecomeFour := rem % 4;
    steps := steps + 1;
    var numFour := rem / 4;
    var aux := 0;
    steps := steps + 1;
    if toBecomeFour != 0 {
      steps := steps + 1;
      if numSeven >= toBecomeFour {
        steps := steps + 3;
        numFour := rem / 4 + 2 * toBecomeFour;
        steps := steps + 1;
        numSeven := numSeven - toBecomeFour;
      } else {
        aux := 1;
      }
    }
    steps := steps + 1;
    if aux == 0 {
      RepeatLen("7", numSeven);
      steps := steps + (|"4"| * numFour + |"7"| * numSeven + |Repeat("7", numSeven)|);
      output := Repeat("4", numFour) + Repeat("7", numSeven);
    } else {
      output := "-1";
    }
  }
}

import opened Prelude

lemma RepeatLen(s: string, k: nat)
  ensures |Repeat(s, k)| == |s| * k
  decreases k
{
  if k > 0 { RepeatLen(s, k - 1); }
}
