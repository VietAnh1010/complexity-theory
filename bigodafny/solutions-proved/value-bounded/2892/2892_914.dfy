// 1228_A. Distinct Digits  (problem 2892, solution 2892_914)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b=map(int,input().split())
// r=[]
// flag=0
// for i in range(a,b+1):
//     tmp=i
//     r=[int(d) for d in str(i)]
//     s=set(r)
//     if(len(r)==len(s)):
//         flag=1
//         break
// if(flag):
//     print(tmp)
// else:
//     print("-1")
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

// number of decimal digits of x (0 for x <= 0)
ghost function ND(x: int): nat
  decreases x
{
  if x <= 0 then 0 else 1 + ND(x / 10)
}

lemma NDMono(x: int, y: int)
  requires x <= y
  ensures ND(x) <= ND(y)
  decreases y
{
  if x > 0 { NDMono(x / 10, y / 10); }
}

ghost function Per(b: int): nat
{
  5 * (ND(b) + 1) + 16 + (ND(b) + 1) * (6 * (ND(b) + 1) + 3)
}

ghost function Range(a: int, b: int): nat
{
  if b >= a then (b - a + 1) as nat else 0
}

lemma SqBound(D: nat, Dm: nat)
  requires D <= Dm
  ensures D * (6 * D + 3) <= Dm * (6 * Dm + 3)
{
  CostMulMonoLeft(D, Dm, 6 * D + 3);
  CostMulMono(Dm, 6 * D + 3, 6 * Dm + 3);
}

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= 4 + Range(a, b) * Per(b) + |output|
{
  steps := 1;
  ghost var P := Per(b);
  ghost var Dm := ND(b) + 1;
  var flag := false;
  var tmp := 0;
  var i := a;
  while i <= b && !flag
    invariant a <= i
    invariant i - a <= Range(a, b)
    invariant steps <= 1 + (i - a) * P
    decreases b - i + 1
  {
    tmp := i;
    var temp := i;
    var digits: seq<int> := [];
    ghost var st := steps;
    NDMono(i, b);
    steps := steps + 4;
    if temp == 0 {
      digits := [0];
      steps := steps + 1;
    } else {
      while temp > 0
        invariant |digits| + ND(temp) == ND(i)
        invariant steps == st + 4 + 5 * |digits|
        decreases temp
      {
        digits := digits + [temp % 10];
        temp := temp / 10;
        steps := steps + 5;
      }
    }
    assert |digits| <= Dm;
    ghost var D := |digits|;
    ghost var M := 6 * D + 3;
    var distinct := true;
    var p := 0;
    ghost var sp := steps;
    steps := steps + 2;
    while p < |digits|
      invariant 0 <= p <= |digits| && D == |digits|
      invariant steps <= sp + 2 + p * M
      decreases |digits| - p
    {
      var q := p + 1;
      ghost var sq := steps;
      while q < |digits|
        invariant p < q <= |digits|
        invariant steps == sq + 6 * (q - p - 1)
        decreases |digits| - q
      {
        if digits[p] == digits[q] { distinct := false; }
        q := q + 1;
        steps := steps + 6;
      }
      CostMulDistrib(p, 1, p + 1, M);
      steps := steps + 3;
      p := p + 1;
    }
    if distinct { flag := true; }
    SqBound(D, Dm);
    assert 5 * D <= 5 * Dm;
    CostMulDistrib(i - a, 1, i - a + 1, P);
    steps := steps + 4;
    i := i + 1;
  }
  if flag {
    output := IntToString(tmp);
    IntToStringDigits(tmp);
    steps := steps + 2 + Digits(tmp);
  } else {
    output := "-1";
    steps := steps + 2 + |output|;
  }
}
