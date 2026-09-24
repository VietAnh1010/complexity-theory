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

ghost predicate Cap(x: int, y: int, s: int)
  requires s >= 0
{
  (InRange(-s, s + 1, x) && y == -s)
  || (x == s + 1 && InRange(-s, s + 1, y))
  || (y == s + 1 && InRange(-(s + 1), s + 1, x))
  || (x == -(s + 1) && InRange(-(s + 1), s + 1, y))
}

lemma CaptureExists(x: int, y: int, s: int)
  requires s >= 0
  requires AbsInt(x) <= s && AbsInt(y) <= s && (AbsInt(x) == s || AbsInt(y) == s)
  ensures Cap(x, y, s) || (s >= 1 && Cap(x, y, s - 1))
{
  if y == -s {
  } else if y == s {
  } else if x == s {
  } else {
  }
}

method Solve(a0: int, b0: int) returns (output: string, ghost steps: nat)
  ensures steps <= 12 * (if AbsInt(a0) > AbsInt(b0) then AbsInt(a0) else AbsInt(b0)) + 15
{
  steps := 0;
  var x := a0; var y := b0;
  ghost var M := if AbsInt(x) > AbsInt(y) then AbsInt(x) else AbsInt(y);
  var U := 1; var D := -1;
  var k := 0; var A := 0; var B := 0;
  var done := false;
  ghost var r := 0;
  while !done
    invariant r >= 0
    invariant !done ==> U == 1 + r && D == -(1 + r)
    invariant !done ==> A == -r && B == -r
    invariant r <= M
    invariant forall s :: 0 <= s < r ==> !Cap(x, y, s)
    invariant !done ==> k == 4 * r
    invariant k <= 4 * r + 4
    invariant steps == 3 * k
    decreases if done then 0 else M - r + 1
  {
    var a := U; var b := B; k := k + 1; steps := steps + 3;
    if InRange(A, a, x) && InRange(B, b, y) { done := true; }
    assert !done ==> !(InRange(A, a, x) && InRange(B, b, y));
    if !done {
      A := a; b := U; k := k + 1; steps := steps + 3;
      if InRange(A, a, x) && InRange(B, b, y) { done := true; }
    }
    if !done {
      B := b; a := D; k := k + 1; steps := steps + 3;
      if InRange(A, a, x) && InRange(B, b, y) { done := true; }
    }
    if !done {
      A := a; b := D; k := k + 1; steps := steps + 3;
      if InRange(A, a, x) && InRange(B, b, y) { done := true; }
    }
    if !done {
      assert !Cap(x, y, r);
      if r == M {
        CaptureExists(x, y, r);
        assert false;
      }
      A := a; B := b;
      U := U + 1; D := D - 1;
      r := r + 1;
    }
  }
  if k < 1 { k := 1; }
  output := IntToString(k - 1);
  steps := steps + 2;
}
