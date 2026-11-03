include "../../prelude.dfy"

lemma ReplaceShrink(s: string, pat: string, rep: string)
  requires |pat| > 0 && |rep| < |pat|
  ensures |ReplaceAll(s, pat, rep)| <= |s|
  ensures |ReplaceAll(s, pat, rep)| == |s| ==> ReplaceAll(s, pat, rep) == s
  decreases |s|
{
  if |s| < |pat| {
  } else if s[0..|pat|] == pat {
    ReplaceShrink(s[|pat|..], pat, rep);
  } else {
    ReplaceShrink(s[1..], pat, rep);
  }
}

lemma ReplaceGrow(s: string, pat: string, rep: string)
  requires |pat| == 1 && |rep| == 2
  ensures |ReplaceAll(s, pat, rep)| <= 2 * |s|
  decreases |s|
{
  if |s| < |pat| {
  } else if s[0..|pat|] == pat {
    ReplaceGrow(s[|pat|..], pat, rep);
  } else {
    ReplaceGrow(s[1..], pat, rep);
  }
}

ghost function RB(L: nat): nat { (L + 1) * (2 * L + 2) }

ghost function TB(n: nat, L: nat): nat { RB(L) + 3 * L + 10 + 6 * n }

ghost function MaxLen(s: seq<string>): nat
  decreases |s|
{
  if |s| == 0 then 0
  else if |s[0]| > MaxLen(s[1..]) then |s[0]| else MaxLen(s[1..])
}

lemma MaxLenBound(s: seq<string>)
  ensures forall k :: 0 <= k < |s| ==> |s[k]| <= MaxLen(s)
  decreases |s|
{
  if |s| > 0 {
    MaxLenBound(s[1..]);
    forall k | 0 <= k < |s| ensures |s[k]| <= MaxLen(s) {
      if k > 0 { assert s[k] == s[1..][k - 1]; }
    }
  }
}

lemma RBMono(m: nat, L: nat)
  requires m <= L
  ensures (m + 1) * (2 * m + 2) <= RB(L)
{
  CostMulMonoLeft(m + 1, L + 1, 2 * m + 2);
  CostMulMono(L + 1, 2 * m + 2, 2 * L + 2);
}

method Reduce(s0: string) returns (result: string, ghost steps: nat)
  ensures steps <= (|s0| + 1) * (2 * |s0| + 2)
  ensures |result| <= |s0|
{
  steps := 0;
  var s := s0;
  var changed := true;
  ghost var K := 2 * |s0| + 2;
  while changed
    invariant |s| <= |s0|
    invariant steps <= (|s0| - |s|) * K + (if changed then 0 else K)
    decreases |s|, changed
  {
    steps := steps + 1;
    steps := steps + |s|;
    var s2 := ReplaceAll(s, "oo", "u");
    ReplaceShrink(s, "oo", "u");
    steps := steps + |s2|;
    var s3 := ReplaceAll(s2, "kh", "h");
    ReplaceShrink(s2, "kh", "h");
    steps := steps + 1;
    if s3 == s {
      changed := false;
    } else {
      assert |s3| < |s|;
      CostMulDistrib(|s0| - |s|, |s| - |s3|, |s0| - |s3|, K);
      CostMulMonoLeft(1, |s| - |s3|, K);
      s := s3;
    }
  }
  result := s;
  CostMulMonoLeft(|s0| - |s|, |s0| + 1, K);
}

method Solve(n: int, names: seq<string>)
    returns (output: string, ghost steps: nat)
  requires n == |names|
  ensures steps <= n * TB(n, MaxLen(names)) + 3 + |output|
{
  steps := 0;
  ghost var L := MaxLen(names);
  ghost var T := TB(n, L);
  MaxLenBound(names);
  var result: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| <= i
    invariant steps <= i * T
    decreases n - i
  {
    ghost var st0 := steps;
    steps := steps + 2;
    steps := steps + 1;
    var str4, s0 := Reduce(names[i]);
    RBMono(|names[i]|, L);
    ghost var r0 := str4;
    steps := steps + s0;
    steps := steps + |str4|;
    ReplaceGrow(r0, "u", "oo");
    str4 := ReplaceAll(str4, "u", "oo");
    ghost var r1 := str4;
    steps := steps + |str4|;
    str4 := ReplaceAll(str4, "h", "kh");
    var exists_ := false;
    var j := 0;
    ghost var s1 := steps;
    while j < |result|
      invariant 0 <= j <= |result|
      invariant steps == s1 + 6 * j
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
    CostMulDistrib(i, 1, i + 1, T);
    i := i + 1;
  }
  steps := steps + 1;
  steps := steps + (1 + Digits(|result|));
  output := IntToString(|result|);
  IntToStringDigits(|result|);
}

import opened Prelude
