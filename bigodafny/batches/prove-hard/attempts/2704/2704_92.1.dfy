// --- Python ---------------------------------------------------------
// def replacement(str):
// 	str2 = str.replace("oo","u")
// 	str3 = str2.replace("kh","h")
// 	if str3 == str:
// 		return str3
// 	else :
// 		str3 = replacement(str3)
// 		return str3
// 	
// 	
// 
// 
// n = int(input())
// myList = []
// myList2 = []
// for i in range(n):
// 	myList.append(input())
// for x in myList:
// 	
// 	str4 = replacement(x)
// 	str4 = str4.replace("u","oo")
// 	str4 = str4.replace("h","kh")
// 	
// 	exist = False
// 	for str in myList2:
// 		if str4 == str:
// 			exist = True
// 	if exist == False:
// 		myList2.append(str4)
// 
// print(len(myList2))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

lemma ReplaceAllShrink(s: string, pat: string, rep: string)
  requires |pat| > 0
  requires |rep| < |pat|
  ensures |ReplaceAll(s, pat, rep)| <= |s|
  ensures |ReplaceAll(s, pat, rep)| == |s| ==> ReplaceAll(s, pat, rep) == s
  decreases |s|
{
  if |s| >= |pat| {
    if s[0..|pat|] == pat {
      ReplaceAllShrink(s[|pat|..], pat, rep);
    } else {
      ReplaceAllShrink(s[1..], pat, rep);
      if |ReplaceAll(s, pat, rep)| == |s| {
        assert ReplaceAll(s, pat, rep) == [s[0]] + ReplaceAll(s[1..], pat, rep);
        assert s == [s[0]] + s[1..];
      }
    }
  }
}

lemma ReplaceAllGrow(s: string, pat: string, rep: string)
  requires |pat| > 0
  requires |rep| <= 2 * |pat|
  ensures |ReplaceAll(s, pat, rep)| <= 2 * |s|
  decreases |s|
{
  if |s| >= |pat| {
    if s[0..|pat|] == pat {
      ReplaceAllGrow(s[|pat|..], pat, rep);
    } else {
      ReplaceAllGrow(s[1..], pat, rep);
    }
  }
}

ghost function RB(m: nat): nat
{
  (m + 1) * (2 * m + 2)
}

lemma RBExpand(m: nat)
  ensures RB(m) == 2 * m * m + 4 * m + 2
{
}

lemma SqStep(i: nat)
  ensures (i + 1) * (i + 1) == i * i + 2 * i + 1
{
}

lemma SqAdd(p: nat, m: nat)
  ensures (p + m) * (p + m) >= p * p + m * m
{
  assert (p + m) * (p + m) == p * p + 2 * p * m + m * m;
  assert p * m >= 0;
}

method Reduce(s0: string) returns (result: string, ghost steps: nat)
  ensures steps <= RB(|s0|)
  ensures |result| <= |s0|
{
  steps := 0;
  var s := s0;
  var changed := true;
  ghost var it: nat := 0;
  ghost var K: nat := 2 * |s0| + 2;
  while changed
    invariant |s| <= |s0|
    invariant it + |s| <= |s0| + (if changed then 0 else 1)
    invariant steps <= it * K
    decreases |s|, (if changed then 1 else 0)
  {
    ghost var it0 := it;
    ghost var steps0 := steps;
    steps := steps + 1;
    steps := steps + |s|;
    var s2 := ReplaceAll(s, "oo", "u");
    ReplaceAllShrink(s, "oo", "u");
    steps := steps + |s2|;
    var s3 := ReplaceAll(s2, "kh", "h");
    ReplaceAllShrink(s2, "kh", "h");
    steps := steps + 1;
    if s3 == s {
      changed := false;
    } else {
      s := s3;
    }
    it := it + 1;
    CostMulDistrib(it0, 1, it, K);
  }
  CostMulMonoLeft(it, |s0| + 1, K);
  result := s;
}

method Solve(n: int, names: seq<string>)
    returns (output: string, ghost steps: nat)
  requires n == |names|
  ensures steps <= 2 * (SumLen(names) * SumLen(names)) + 7 * SumLen(names) + 14 * n + 6 * (n * n) + |output| + 2
{
  steps := 0;
  var result: seq<string> := [];
  var i := 0;
  ghost var P: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| <= i
    invariant P == SumLen(names[..i])
    invariant steps <= 2 * (P * P) + 7 * P + 14 * i + 6 * (i * i)
    decreases n - i
  {
    ghost var steps0 := steps;
    ghost var m := |names[i]|;
    SumLenSnoc(names[..i], names[i]);
    assert names[..i + 1] == names[..i] + [names[i]];
    SqAdd(P, m);
    SqStep(i);
    RBExpand(m);
    steps := steps + 2;
    steps := steps + 1;
    var str4, s0 := Reduce(names[i]);
    steps := steps + s0;
    steps := steps + |str4|;
    ReplaceAllGrow(str4, "u", "oo");
    str4 := ReplaceAll(str4, "u", "oo");
    steps := steps + |str4|;
    str4 := ReplaceAll(str4, "h", "kh");
    var exists_ := false;
    var j := 0;
    ghost var stepsIn := steps;
    while j < |result|
      invariant 0 <= j <= |result|
      invariant steps == stepsIn + 6 * j
      decreases |result| - j
    {
      steps := steps + 3;
      steps := steps + 2;
      if result[j] == str4 {
        exists_ := true;
      }
      steps := steps + 1;
      j := j + 1;
    }
    steps := steps + 2;
    steps := steps + 1;
    if !exists_ {
      steps := steps + (1 + |[str4]|);
      result := result + [str4];
    }
    steps := steps + 1;
    i := i + 1;
    P := P + m;
  }
  assert names[..n] == names;
  IntToStringDigits(|result|);
  steps := steps + 1;
  steps := steps + (1 + Digits(|result|));
  output := IntToString(|result|);
}

import opened Prelude
