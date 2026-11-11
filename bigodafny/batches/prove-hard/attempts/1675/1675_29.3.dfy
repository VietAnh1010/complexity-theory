// --- Python ---------------------------------------------------------
// s=input()
// t=input()
// x=set(s)
// s=list(s)
// i=0
// j=0
// nt=0
// ar=0
// at=0
// while i<=len(s) and j<len(t):
// 	if i==len(s):
// 			i=0
// 			ar=1
// 	if t[j] in s:
// 		if s[i]==t[j]:
// 			s[i]=':'
// 			j+=1
// 			i+=1
// 		else:
// 			i+=1
// 			at=1
// 	else:
// 		nt=1
// 		break
// if nt==0 and len(s)==len(t):
// 	at=0
// else:
// 	at=1
// if nt==1:
// 	print('need tree')
// elif at==ar==1:
// 	print('both')
// elif at==1:
// 	print('automaton')
// elif ar==1:
// 	print('array')
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

ghost function Q(i: int, w: bool, m: int): int { i + (if w then m + 2 else 0) }

lemma MulStep(k: nat, c: nat)
  ensures (k + 1) * c == k * c + c
{}

lemma MulMono(a: nat, b: nat, c: nat)
  requires a <= b
  ensures a * c <= b * c
{
  assert b * c == a * c + (b - a) * c;
  assert (b - a) * c >= 0;
}

lemma Final(steps: nat, k: nat, j: nat, t: nat, w: nat, c: nat)
  requires j <= t
  requires k <= j * w + w
  requires steps <= k * c
  ensures steps <= (t * w + w) * c
{
  MulMono(j, t, w);
  MulMono(k, t * w + w, c);
}

method Solve(v0: string, v1: string)
    returns (output: string, ghost steps: nat)
  requires |v0| >= 1
  ensures steps <= (|v1| * (2 * |v0| + 3) + (2 * |v0| + 3)) * (7 * |v0| + 20) + 20
{
  steps := 0;
  var s := v0;
  var t := v1;
  var i := 0;
  var j := 0;
  var nt := 0;
  var ar := 0;
  var at := 0;
  var done := false;
  ghost var w := false;
  ghost var K: nat := 0;
  ghost var C: nat := 7 * |v0| + 20;
  ghost var W: nat := 2 * |v0| + 3;
  while i <= |s| && j < |t| && !done
    invariant 0 <= i <= |s|
    invariant 0 <= j <= |t|
    invariant |s| == |v0|
    invariant w && !done ==> j < |t| && exists k :: i <= k < |s| && s[k] == t[j]
    invariant steps <= K * C
    invariant C == 7 * |v0| + 20 && W == 2 * |v0| + 3
    invariant K <= j * W + Q(i, w, |v0|) + (if done then 1 else 0)
    decreases (if done then 0 else 1), |t| - j, (if w then 0 else 1), |s| - i
  {
    ghost var sb := steps;
    MulStep(K, C);
    MulStep(j, W);
    K := K + 1;
    steps := steps + (5 + (if i <= |s| then 2 else 0) + if i <= |s| && j < |t| then 1 else 0);
    steps := steps + 2;
    if i == |s| {
      i := 0;
      ar := 1;
      w := true;
    }
    var found := false;
    var idx := 0;
    ghost var s0 := steps;
    while idx < |s|
      invariant 0 <= idx <= |s|
      invariant steps == s0 + 7 * idx
      invariant found <==> exists k :: 0 <= k < idx && s[k] == t[j]
      decreases |s| - idx
    {
      steps := steps + 3;
      steps := steps + 3;
      if s[idx] == t[j] {
        found := true;
      }
      steps := steps + 1;
      idx := idx + 1;
    }
    steps := steps + 2;
    if found {
      steps := steps + 3;
      if s[i] == t[j] {
        steps := steps + 1;
        s := s[i := ':'];
        steps := steps + 1;
        j := j + 1;
        w := false;
        steps := steps + 1;
        i := i + 1;
      } else {
        steps := steps + 1;
        i := i + 1;
        at := 1;
      }
    } else {
      nt := 1;
      done := true;
    }
    assert steps <= sb + C;
  }
  Final(steps, K, j, |t|, W, C);
  steps := steps + (4 + (if i <= |s| then 2 else 0) + if i <= |s| && j < |t| then 1 else 0);
  steps := steps + (2 + if nt == 0 then 3 else 0);
  if nt == 0 && |s| == |t| {
    at := 0;
  } else {
    at := 1;
  }
  steps := steps + 1;
  if nt == 1 {
    output := "need tree";
  } else if at == 1 && ar == 1 {
    output := "both";
  } else if at == 1 {
    output := "automaton";
  } else if ar == 1 {
    output := "array";
  } else {
    output := "";
  }
}

import opened Prelude
