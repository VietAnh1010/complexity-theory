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

include "../../../../prelude.dfy"

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= n * n + 6 * n + 60
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
      RepeatLen('7', numSeven);
      RepeatSteps('4', numFour);
      RepeatSteps('7', numSeven);
      SqMono(numSeven, n);
      steps := steps + (Repeat_steps('4', numFour) + Repeat_steps('7', numSeven) + |Repeat('7', numSeven)|);
      output := Repeat('4', numFour) + Repeat('7', numSeven);
    } else {
      output := "-1";
    }
  }
}

function Repeat(c: char, n: int): string
  decreases if n < 0 then 0 else n
{
  if n <= 0 then
    ""
  else
    [c] + Repeat(c, n - 1)
}

ghost function Repeat_steps(c: char, n: int): nat
  decreases if n < 0 then 0 else n
{
  2 + if n <= 0 then 0 else 2 + Repeat_steps(c, n - 1) + |Repeat(c, n - 1)|
}

lemma RepeatLen(c: char, n: int)
  ensures |Repeat(c, n)| == (if n < 0 then 0 else n)
  decreases if n < 0 then 0 else n
{
  if n > 0 { RepeatLen(c, n - 1); }
}

lemma RepeatSteps(c: char, n: int)
  ensures Repeat_steps(c, n) <= 2 + 4 * (if n < 0 then 0 else n) + (if n < 0 then 0 else n) * (if n < 0 then 0 else n)
  decreases if n < 0 then 0 else n
{
  if n > 0 {
    RepeatSteps(c, n - 1);
    RepeatLen(c, n - 1);
    SqStep(n - 1);
  }
}

lemma SqStep(m: nat)
  ensures (m + 1) * (m + 1) == m * m + 2 * m + 1
{}

lemma SqMono(a: int, b: int)
  requires 0 <= a <= b
  ensures a * a <= b * b
{}

import opened Prelude
