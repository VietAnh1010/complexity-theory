// 630_F. Selection of Personnel  (problem 2286, solution 2286_319)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def fac(x):
// 	p = 1
// 	for i in range(2, x + 1):
// 		p *= i
// 	return p
// 
// 
// def c(n, k):
// 	return fac(n) // (fac(k) * fac(n - k))
// 
// n = int(input())
// print(c(n, 5) + c(n, 6) + c(n, 7))
// 
//  	 								 	     			   	 		 		
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var c5 := C2286(n, 5);
  var c6 := C2286(n, 6);
  var c7 := C2286(n, 7);
  output := IntToString(c5 + c6 + c7);
}

method C2286(n: int, k: int) returns (r: int)
{
  var fn := Fac2286(n);
  var fk := Fac2286(k);
  var fnk := Fac2286(n - k);
  r := fn / (fk * fnk);
}

method Fac2286(x: int) returns (p: int)
{
  p := 1;
  var i := 2;
  while i <= x
    decreases x - i
  {
    p := p * i;
    i := i + 1;
  }
}
