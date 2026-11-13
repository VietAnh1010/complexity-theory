include "../../prelude.dfy"
import opened Prelude

function ContainsFrom(s: string, pat: string, i: int): bool
  requires 0 <= i <= |s|
  requires |pat| > 0
  decreases |s| - i
{
  if i > |s| - |pat| then false
  else if s[i..i + |pat|] == pat then true
  else ContainsFrom(s, pat, i + 1)
}

function ContainsSub(s: string, pat: string): bool
  requires |pat| > 0
{
  ContainsFrom(s, pat, 0)
}

lemma ReplaceShrink(s: string, pat: string, rep: string)
  requires |pat| > 0 && |rep| < |pat|
  ensures |ReplaceAll(s, pat, rep)| <= |s|
  decreases |s|
{
  if |s| < |pat| {
  } else if s[0..|pat|] == pat {
    ReplaceShrink(s[|pat|..], pat, rep);
  } else {
    ReplaceShrink(s[1..], pat, rep);
  }
}

lemma ReplaceStrict(t: string, pat: string, rep: string, j: int)
  requires |pat| > 0 && |rep| < |pat|
  requires 0 <= j <= |t| - |pat| && t[j..j + |pat|] == pat
  ensures |ReplaceAll(t, pat, rep)| < |t|
  decreases |t|
{
  if t[0..|pat|] == pat {
    ReplaceShrink(t[|pat|..], pat, rep);
  } else {
    assert j > 0;
    assert t[1..][j - 1..j - 1 + |pat|] == t[j..j + |pat|];
    ReplaceStrict(t[1..], pat, rep, j - 1);
  }
}

lemma ContainsWitness(s: string, pat: string, i: int) returns (j: int)
  requires 0 <= i <= |s| && |pat| > 0
  requires ContainsFrom(s, pat, i)
  ensures i <= j <= |s| - |pat| && s[j..j + |pat|] == pat
  decreases |s| - i
{
  if s[i..i + |pat|] != pat {
    j := ContainsWitness(s, pat, i + 1);
  } else {
    j := i;
  }
}

lemma ReplaceGrow(s: string)
  ensures |ReplaceAll(s, "u", "oo")| <= 2 * |s|
  decreases |s|
{
  if |s| < 1 {
  } else if s[0..1] == "u" {
    ReplaceGrow(s[1..]);
  } else {
    ReplaceGrow(s[1..]);
  }
}

lemma QuadFacts(m: nat)
  ensures (2 * m) * (16 * m + 10) == 32 * (m * m) + 20 * m
{
}

method Normalize(word: string) returns (result: string, ghost steps: nat)
  ensures steps <= 40 * (|word| * |word|) + 40 * |word| + 40
{
  var w := ReplaceAll(word, "u", "oo");
  ReplaceGrow(word);
  steps := |word| + 1;
  ghost var W := 2 * |word|;
  ghost var K := 8 * W + 10;
  ghost var it: nat := 0;
  ghost var base := steps;
  while ContainsSub(w, "kkh")
    invariant |w| <= W
    invariant it + |w| <= W
    invariant steps <= base + it * K
    decreases |w|
  {
    ghost var j := ContainsWitness(w, "kkh", 0);
    ReplaceStrict(w, "kkh", "kh", j);
    ghost var oldLen := |w|;
    w := ReplaceAll(w, "kkh", "kh");
    CostMulDistrib(it, 1, it + 1, K);
    steps := steps + 5 * oldLen + 5 + oldLen + 1;
    it := it + 1;
  }
  CostMulMonoLeft(it, W, K);
  steps := steps + 5 * |w| + 5;
  if ContainsSub(w, "kh") {
    ReplaceShrink(w, "kh", "h");
    w := ReplaceAll(w, "kh", "h");
    steps := steps + |w| * 0 + 2 * W + 1;
  }
  QuadFacts(|word|);
  result := w;
}

ghost function Bnd(xs: seq<string>): nat
  decreases |xs|
{
  if |xs| == 0 then 0
  else Bnd(xs[..|xs| - 1]) + 40 * (|xs[|xs| - 1]| * |xs[|xs| - 1]|) + 40 * |xs[|xs| - 1]| + 45
}

method Solve(n: int, names: seq<string>) returns (output: string, ghost steps: nat)
  requires n == |names|
  ensures steps <= Bnd(names) + 3 + |output|
{
  steps := 1;
  var seen: set<string> := {};
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= Bnd(names[..i]) + 1
    decreases n - i
  {
    var w, st := Normalize(names[i]);
    seen := seen + {w};
    assert names[..i + 1][..i] == names[..i];
    steps := steps + st + 4;
    i := i + 1;
  }
  assert names[..i] == names;
  output := IntToString(|seen|);
  IntToStringDigits(|seen|);
  steps := steps + Digits(|seen|);
}
