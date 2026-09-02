// 279_A. Point on Spiral  (problem 2847, solution 2847_36)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// U=1
// D=-1
// x,y=map(int,input().split())
// k=A=B=0
// while 1:
// 	a,b=U,B;k+=1
// 	if (A<=x<=a or a<=x<=A)and(B<=y<=b or b<=y<=B):break
// 	A=a;b=U;k+=1
// 	if (A<=x<=a or a<=x<=A)and(B<=y<=b or b<=y<=B):break
// 	B=b;a=D;k+=1
// 	if (A<=x<=a or a<=x<=A)and(B<=y<=b or b<=y<=B):break
// 	A=a;b=D;k+=1
// 	if (A<=x<=a or a<=x<=A)and(B<=y<=b or b<=y<=B):break
// 	A,B=a,b
// 	U+=1;D-=1
// if k<1:k=1
// print(k-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

predicate InRange(p: int, q: int, v: int)
{
  (p <= v && v <= q) || (q <= v && v <= p)
}

method Solve(a0: int, b0: int) returns (output: string)
  decreases *
{
  var x := a0; var y := b0;
  var U := 1; var D := -1;
  var k := 0; var A := 0; var B := 0;
  var done := false;
  while !done
    decreases *
  {
    var a := U; var b := B; k := k + 1;
    if InRange(A, a, x) && InRange(B, b, y) { done := true; }
    if !done {
      A := a; b := U; k := k + 1;
      if InRange(A, a, x) && InRange(B, b, y) { done := true; }
    }
    if !done {
      B := b; a := D; k := k + 1;
      if InRange(A, a, x) && InRange(B, b, y) { done := true; }
    }
    if !done {
      A := a; b := D; k := k + 1;
      if InRange(A, a, x) && InRange(B, b, y) { done := true; }
    }
    if !done {
      A := a; B := b;
      U := U + 1; D := D - 1;
    }
  }
  if k < 1 { k := 1; }
  output := IntToString(k - 1);
}
