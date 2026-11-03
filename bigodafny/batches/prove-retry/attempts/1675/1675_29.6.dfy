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

ghost function PP(w: bool, n: nat, i: nat): nat
{
  if w then n + 1 + i else i
}

ghost function Pot(j: nat, m: nat, p: nat): nat
{
  j * m + p
}

lemma PotStep(j: nat, m: nat, p: nat, p2: nat)
  requires p < p2
  ensures Pot(j, m, p) < Pot(j, m, p2)
{
}

lemma PotJump(j: nat, m: nat, p: nat, p2: nat)
  requires p < m
  ensures Pot(j, m, p) < Pot(j + 1, m, p2)
{
  CostMulDistrib(j, 1, j + 1, m);
}

lemma PotBound(j: nat, T: nat, m: nat, p: nat)
  requires j <= T && p < m
  ensures Pot(j, m, p) < (T + 1) * m
{
  CostMulMonoLeft(j, T, m);
  CostMulDistrib(T, 1, T + 1, m);
}

method Solve(v0: string, v1: string)
    returns (output: string, ghost steps: nat)
  requires |v0| >= 1
  ensures steps <= (|v1| + 1) * (2 * |v0| + 2) * (7 * |v0| + 19) + 13
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
  ghost var c := 0;
  while i <= |s| && j < |t| && !done
    invariant 0 <= i <= |s|
    invariant 0 <= j <= |t|
    invariant |s| == |v0|
    invariant 0 <= c
    invariant w ==> (j < |t| ==> forall q :: 0 <= q < i ==> s[q] != t[j])
    invariant c <= Pot(j, 2 * |s| + 2, PP(w, |s|, i)) + (if done then 1 else 0)
    invariant steps <= c * (7 * |s| + 19)
    decreases (|t| + 1) * (2 * |s| + 2) - Pot(j, 2 * |s| + 2, PP(w, |s|, i)), if done then 0 else 1
  {
    ghost var st := steps;
    ghost var jOld := j;
    ghost var pOld := PP(w, |s|, i);
    ghost var stuck := i == |s| && w;
    assert stuck ==> forall q :: 0 <= q < |s| ==> s[q] != t[j];
    PotBound(j, |t|, 2 * |s| + 2, PP(w, |s|, i));
    steps := steps + (5 + (if i <= |s| then 2 else 0) + if i <= |s| && j < |t| then 1 else 0);
    steps := steps + 2;
    if i == |s| {
      i := 0;
      ar := 1;
      w := true;
    }
    var found := false;
    var idx := 0;
    while idx < |s|
      invariant 0 <= idx <= |s|
      invariant found <==> exists q :: 0 <= q < idx && s[q] == t[j]
      invariant steps == st + 10 + 7 * idx
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
    assert stuck ==> !found;
    steps := steps + 2;
    if found {
      steps := steps + 3;
      if s[i] == t[j] {
        steps := steps + 1;
        s := s[i := ':'];
        steps := steps + 1;
        j := j + 1;
        steps := steps + 1;
        i := i + 1;
        w := false;
      } else {
        steps := steps + 1;
        i := i + 1;
        at := 1;
      }
    } else {
      nt := 1;
      done := true;
    }
    CostMulDistrib(c, 1, c + 1, 7 * |s| + 19);
    if !done && j == jOld {
      PotStep(j, 2 * |s| + 2, pOld, PP(w, |s|, i));
    } else if !done {
      PotJump(j, 2 * |s| + 2, pOld, PP(w, |s|, i));
    }
    c := c + 1;
  }
  PotBound(j, |t|, 2 * |s| + 2, PP(w, |s|, i));
  CostMulMonoLeft(c, (|t| + 1) * (2 * |s| + 2), 7 * |s| + 19);
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
