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

ghost predicate Has(s: string, c: char) {
  exists p :: 0 <= p < |s| && s[p] == c
}

ghost function Nxt(s: string, c: char, i: nat): nat
  decreases |s| - i
{
  if i >= |s| then 0 else if s[i] == c then 0 else 1 + Nxt(s, c, i + 1)
}

ghost function Meas(s: string, c: char, i: nat): nat
  requires i <= |s|
{
  if i + Nxt(s, c, i) < |s| then Nxt(s, c, i) else (|s| - i) + 1 + Nxt(s, c, 0)
}

lemma NxtFacts(s: string, c: char, i: nat)
  requires i <= |s|
  ensures i + Nxt(s, c, i) <= |s|
  ensures i + Nxt(s, c, i) < |s| ==> s[i + Nxt(s, c, i)] == c
  ensures i + Nxt(s, c, i) == |s| ==> forall p :: i <= p < |s| ==> s[p] != c
  decreases |s| - i
{
  if i < |s| && s[i] != c {
    NxtFacts(s, c, i + 1);
  }
}

lemma HasNxt(s: string, c: char)
  requires Has(s, c)
  ensures Nxt(s, c, 0) < |s|
{
  NxtFacts(s, c, 0);
}

lemma Reset(s: string, c: char)
  requires Has(s, c)
  ensures Meas(s, c, 0) < Meas(s, c, |s|)
{
  HasNxt(s, c);
}

lemma Adv(s: string, c: char, i: nat)
  requires Has(s, c)
  requires i < |s|
  requires s[i] != c
  ensures Meas(s, c, i + 1) < Meas(s, c, i)
{
  NxtFacts(s, c, i + 1);
  HasNxt(s, c);
}

lemma Bnd(s: string, c: char, i: nat)
  requires i <= |s|
  ensures Meas(s, c, i) <= 2 * |s| + 1
{
  NxtFacts(s, c, i);
  NxtFacts(s, c, 0);
}

lemma MulSucc(a: nat, b: nat)
  ensures (a + 1) * b == a * b + b
{
}

lemma MulMono(a: nat, b: nat, k: nat)
  requires a <= b
  ensures a * k <= b * k
{
  var d := b - a;
  assert b * k == a * k + d * k;
}

method Solve(v0: string, v1: string)
    returns (output: string, ghost steps: nat)
  requires |v0| >= 1
  ensures steps <= (|v1| + 1) * (2 * |v0| + 3) * (20 + 7 * |v0|) + 13
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
  ghost var c: nat := 0;
  ghost var tot: nat := 0;
  ghost var base: nat := 0;
  if j < |t| && Has(s, t[j]) {
    Bnd(s, t[j], i);
  }
  while i <= |s| && j < |t| && !done
    invariant 0 <= i <= |s|
    invariant 0 <= j <= |t|
    invariant |s| == |v0|
    invariant base == j * (2 * |v0| + 3)
    invariant tot <= base + c
    invariant steps <= tot * (20 + 7 * |v0|)
    invariant c + (if j < |t| && Has(s, t[j]) then Meas(s, t[j], i) else 0) <= 2 * |v0| + 2
    invariant (!done && !(j < |t| && Has(s, t[j]))) ==> c == 0
    decreases |t| - j, (if done then 0 else 1),
      (if done || j >= |t| || !Has(s, t[j]) then 0 else Meas(s, t[j], i))
  {
    ghost var tot0 := tot;
    ghost var st0 := steps;
    ghost var j0 := j;
    ghost var ch := t[j];
    ghost var m0 := Meas(s, ch, i);
    c := c + 1;
    tot := tot + 1;
    MulSucc(tot0, 20 + 7 * |v0|);
    steps := steps + (5 + (if i <= |s| then 2 else 0) + if i <= |s| && j < |t| then 1 else 0);
    steps := steps + 2;
    if i == |s| {
      i := 0;
      ar := 1;
      if Has(s, ch) {
        Reset(s, ch);
      }
    }
    ghost var m1 := Meas(s, ch, i);
    var found := false;
    var idx := 0;
    ghost var stI := steps;
    while idx < |s|
      invariant 0 <= idx <= |s|
      invariant steps == stI + 7 * idx
      invariant found <==> (exists p :: 0 <= p < idx && s[p] == t[j])
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
        steps := steps + 1;
        i := i + 1;
        MulSucc(j0, 2 * |v0| + 3);
        base := base + (2 * |v0| + 3);
        c := 0;
        if j < |t| && Has(s, t[j]) {
          Bnd(s, t[j], i);
        }
      } else {
        Adv(s, ch, i);
        steps := steps + 1;
        i := i + 1;
        at := 1;
      }
    } else {
      nt := 1;
      done := true;
    }
  }
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
  MulMono(j, |t|, 2 * |v0| + 3);
  assert tot <= (|t| + 1) * (2 * |v0| + 3) by {
    MulSucc(|t|, 2 * |v0| + 3);
  }
  MulMono(tot, (|t| + 1) * (2 * |v0| + 3), 20 + 7 * |v0|);
}

import opened Prelude
