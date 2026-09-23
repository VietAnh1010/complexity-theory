// 630_G. Challenge Pennants  (problem 1077, solution 1077_84)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def Fact(n):
//   res = 1 
//   while n > 0 :
//     res *= n
//     n -= 1
//   return res
// 
// def C(n,k):
//   return (Fact(n) // ( Fact(k) * Fact(n-k) ) )
//   
// n = int ( input() ) - 1 
// 
// print ( C(n+5,n)*C(n+3,3) )
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= 4 * n + |output| + 40
{
  var m := n - 1;
  var a1 := m + 5;
  var k1 := m;
  ghost var f1steps;
  var fa1;
  f1steps, fa1 := FactorialM(a1);
  ghost var f2steps;
  var fk1;
  f2steps, fk1 := FactorialM(k1);
  ghost var f3steps;
  var fak1;
  f3steps, fak1 := FactorialM(a1 - k1);
  var c1 := FloorDiv(fa1, fk1 * fak1);
  var a2 := m + 3;
  var k2 := 3;
  ghost var f4steps;
  var fa2;
  f4steps, fa2 := FactorialM(a2);
  ghost var f5steps;
  var fk2;
  f5steps, fk2 := FactorialM(k2);
  ghost var f6steps;
  var fak2;
  f6steps, fak2 := FactorialM(a2 - k2);
  var c2 := FloorDiv(fa2, fk2 * fak2);
  output := IntToString(c1 * c2);
  steps := f1steps + f2steps + f3steps + f4steps + f5steps + f6steps
         + |output| + 10;
}

// Charge one unit per multiplicative step of the loop, matching the Python
// `while n > 0: res *= n; n -= 1`.
method FactorialM(a: int) returns (ghost steps: nat, res: int)
  requires a >= 0
  ensures res >= 1
  ensures steps <= a + 2
{
  res := 1;
  var nn := a;
  steps := 1;
  ghost var base1 := steps;
  ghost var cnt := 0;
  while nn > 0
    invariant res >= 1
    invariant 0 <= nn <= a
    invariant cnt == a - nn
    invariant steps <= base1 + cnt
    decreases nn
  {
    res := res * nn;
    nn := nn - 1;
    cnt := cnt + 1;
    steps := steps + 1;
  }
}
