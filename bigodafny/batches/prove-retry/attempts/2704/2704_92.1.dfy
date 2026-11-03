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
      CostMulDistrib(|s0| - |s|, 1, |s0| - |s3|, K);
      s := s3;
    }
  }
  result := s;
  CostMulMonoLeft(|s0| - |s|, |s0| + 1, K);
}

method Solve(n: int, names: seq<string>) returns (output: string)
  requires n == |names|
  decreases *
{
  var result: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var str4 := Reduce(names[i]);
    str4 := ReplaceAll(str4, "u", "oo");
    str4 := ReplaceAll(str4, "h", "kh");
    var exists_ := false;
    var j := 0;
    while j < |result|
      invariant 0 <= j <= |result|
      decreases |result| - j
    {
      if result[j] == str4 { exists_ := true; }
      j := j + 1;
    }
    if !exists_ {
      result := result + [str4];
    }
    i := i + 1;
  }
  output := IntToString(|result|);
}
