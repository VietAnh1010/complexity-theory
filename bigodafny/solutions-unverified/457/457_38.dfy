// 355_A. Vasya and Digital Root  (problem 457, solution 457_38)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l=input().split()
// k=int(l[0])
// d=int(l[1])
// if(k==1 and d==0):
// 	print(0)
// elif(k!=1 and d==0):
// 	print('No solution')
// else:
// 	i=1
// 	n=d
// 	while len(str(n))!=k:
// 		n+=9**(i)
// 		i+=1
// 	print(n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int) returns (output: string)
  requires n >= 1
  requires 0 <= m <= 9
{
  var k := n;
  var d := m;
  if k == 1 && d == 0 {
    output := "0\n";
  } else if k != 1 && d == 0 {
    output := "No solution\n";
  } else {
    var nn := d;
    var pow := 9;
    while NumDigits(nn) != k
      invariant nn >= 0
      decreases if k - NumDigits(nn) >= 0 then k - NumDigits(nn) else NumDigits(nn) - k
    {
      nn := nn + pow;
      pow := pow * 9;
    }
    output := IntToString(nn) + "\n";
  }
}

function NumDigits(x: int): int
  requires x >= 0
  decreases x
{
  if x < 10 then 1 else 1 + NumDigits(x / 10)
}
