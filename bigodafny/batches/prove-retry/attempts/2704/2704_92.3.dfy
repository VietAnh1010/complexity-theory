include "../../prelude.dfy"
import opened Prelude

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

method Reduce(s0: string) returns (result: string, ghost steps: nat)
  ensures steps <= (|s0| + 2) * (3 * |s0| + 8) + 2
  ensures |result| <= |s0|
{
  steps := 1;
  var s := s0;
  var changed := true;
  ghost var K := 3 * |s0| + 8;
  while changed
    invariant |s| <= |s0|
    invariant steps <= 1 + (|s0| - |s|) * K + (if changed then 0 else K)
    decreases |s|, changed
  {
    ReplaceShrink(s, "oo", "u");
    var s2 := ReplaceAll(s, "oo", "u");
    ReplaceShrink(s2, "kh", "h");
    var s3 := ReplaceAll(s2, "kh", "h");
    steps := steps + (|s| + 1) + (|s2| + 1) + |s| + 4;
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

ghost function RB(L: nat): nat { (L + 2) * (3 * L + 8) + 2 }

ghost function TB(n: nat, L: nat): nat { RB(L) + 6 * L + 20 + n * (4 * L + 6) }

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
  ensures (m + 2) * (3 * m + 8) + 2 <= RB(L)
{
  CostMulMonoLeft(m + 2, L + 2, 3 * m + 8);
  CostMulMono(L + 2, 3 * m + 8, 3 * L + 8);
}

method Solve(n: int, names: seq<string>) returns (output: string, ghost steps: nat)
  requires n == |names|
  ensures steps <= n * TB(n, MaxLen(names)) + 20 + |output|
{
  steps := 2;
  ghost var L := MaxLen(names);
  ghost var T := TB(n, L);
  ghost var Q := 4 * L + 6;
  MaxLenBound(names);
  var result: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| <= i
    invariant forall k :: 0 <= k < |result| ==> |result[k]| <= 4 * L
    invariant steps <= 2 + i * T
    decreases n - i
  {
    ghost var s0 := steps;
    var str4, rs := Reduce(names[i]);
    RBMono(|names[i]|, L);
    ReplaceGrow(str4, "u", "oo");
    var str5 := ReplaceAll(str4, "u", "oo");
    ReplaceGrow(str5, "h", "kh");
    var str6 := ReplaceAll(str5, "h", "kh");
    steps := steps + rs + (|str4| + 1) + (|str5| + 1) + 6;
    ghost var s1 := steps;
    var exists_ := false;
    var j := 0;
    while j < |result|
      invariant 0 <= j <= |result|
      invariant steps <= s1 + j * Q
      decreases |result| - j
    {
      if result[j] == str6 { exists_ := true; }
      steps := steps + (|str6| + 1) + 4;
      CostMulDistrib(j, 1, j + 1, Q);
      j := j + 1;
    }
    CostMulMonoLeft(j, n, Q);
    if !exists_ {
      result := result + [str6];
    }
    steps := steps + 5;
    CostMulDistrib(i, 1, i + 1, T);
    i := i + 1;
  }
  output := IntToString(|result|);
  IntToStringDigits(|result|);
  steps := steps + |output|;
}
