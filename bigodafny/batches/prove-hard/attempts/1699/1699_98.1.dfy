// --- Python ---------------------------------------------------------
//
// n=int(input())
// l=[1,1]
// b=""
// for i in range(2,n+1):
// 	l.append(l[i-2]+l[i-1])
// for j in range(1,n+1):
// 	if j in l:
// 		b+="O"
// 	else:
// 		b+="o"
// print(b)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

ghost function Mx(n: int): nat { if n > 0 then n else 0 }

lemma MulStep(a: nat, K: nat)
  ensures (a + 1) * K == a * K + K
{}

lemma MulDist(m: nat)
  ensures m * (6 * m + 19) == 6 * m * m + 19 * m
{}

lemma MulMono(a: nat, b: nat, K: nat)
  requires a <= b
  ensures a * K <= b * K
{}

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 6 * Mx(n) * Mx(n) + 32 * Mx(n) + 4
{
  steps := 0;
  steps := steps + 2;
  var l := [1, 1];
  var i := 2;
  while i <= n
    invariant 2 <= i
    invariant |l| == i
    invariant i <= Mx(n) + 2
    invariant steps <= 2 + 11 * (i - 2)
    decreases n - i + 1
  {
    steps := steps + 2;
    steps := steps + (6 + |[l[i - 2] + l[i - 1]]|);
    l := l + [l[i - 2] + l[i - 1]];
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  var parts: seq<string> := [];
  var j := 1;
  ghost var s1 := steps;
  ghost var bigK: nat := 6 * Mx(n) + 19;
  while j <= n
    invariant 1 <= j <= Mx(n) + 1
    invariant |parts| == j - 1
    invariant SumLen(parts) == |parts|
    invariant |l| <= Mx(n) + 2
    invariant s1 <= 11 * Mx(n) + 3
    invariant steps <= s1 + (j - 1) * bigK
    invariant bigK == 6 * Mx(n) + 19
    decreases n - j + 1
  {
    steps := steps + 2;
    var found := false;
    var k := 0;
    ghost var s0 := steps;
    while k < |l|
      invariant 0 <= k <= |l|
      invariant steps == s0 + 6 * k
      decreases |l| - k
    {
      steps := steps + 3;
      steps := steps + 2;
      if l[k] == j {
        found := true;
      }
      steps := steps + 1;
      k := k + 1;
    }
    steps := steps + 2;
    if found {
      steps := steps + (1 + |["O"]|);
      SumLenSnoc(parts, "O");
      parts := parts + ["O"];
    } else {
      steps := steps + (1 + |["o"]|);
      SumLenSnoc(parts, "o");
      parts := parts + ["o"];
    }
    steps := steps + 1;
    MulStep(j - 1, bigK);
    j := j + 1;
  }
  steps := steps + 1;
  MulMono(j - 1, Mx(n), bigK);
  MulDist(Mx(n));
  steps := steps + (SumLen(parts) + |parts|);
  output := Join(parts, "");
}

import opened Prelude
