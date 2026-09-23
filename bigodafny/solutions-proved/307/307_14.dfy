// 729_A. Interview with Oleg  (problem 307, solution 307_14)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// for i in range(100, 0, -1):
//     s = s.replace('o' + 'go' * i, '***')
// print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function RepeatGo(i: int): string
  requires i >= 0
  decreases i
{
  if i == 0 then "" else "go" + RepeatGo(i - 1)
}

lemma RepeatGoLen(i: int)
  requires i >= 0
  ensures |RepeatGo(i)| == 2 * i
  decreases i
{
  if i == 0 {
  } else {
    RepeatGoLen(i - 1);
  }
}

// The outer loop runs a literal 100 times regardless of input -- a constant
// per COMPLEXITY.md's value-vs-size convention -- so its only effect on the
// bound is a constant factor. What has to be proved instead is that ReplaceAll
// never grows the string: |rep| <= |pat| holds for every i in [1,100] because
// pat = "o" + "go"*i has length 2*i+1 >= 3 = |rep|. That keeps |cur| <= |s|
// across all 100 passes, so each pass costs O(|s|) and the total is O(|s|).
method ReplaceAll(s: string, pat: string, rep: string) returns (res: string, ghost steps: nat)
  requires |pat| > 0
  requires |rep| <= |pat|
  ensures |res| <= |s|
  ensures steps <= 4 * |s| + 3
{
  steps := 1;
  var parts: seq<string> := [];
  var i := 0;
  ghost var outLen: nat := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant outLen <= i
    invariant SumPartsLen(parts) == outLen
    invariant steps <= 1 + 4 * i
    decreases |s| - i
  {
    if i + |pat| <= |s| && s[i..i+|pat|] == pat {
      SumPartsLenSnoc(parts, rep);
      parts := parts + [rep];
      outLen := outLen + |rep|;
      i := i + |pat|;
      steps := steps + 4;
    } else {
      SumPartsLenSnoc(parts, [s[i]]);
      parts := parts + [[s[i]]];
      outLen := outLen + 1;
      i := i + 1;
      steps := steps + 3;
    }
  }
  res := Join(parts, "");
  JoinEmptySepLen(parts);
  assert |res| == outLen;
  steps := steps + 1;
}

lemma SumPartsLenSnoc(parts: seq<string>, extra: string)
  ensures SumPartsLen(parts + [extra]) == SumPartsLen(parts) + |extra|
  decreases |parts|
{
  if |parts| == 0 {
  } else {
    assert (parts + [extra])[1..] == parts[1..] + [extra];
    SumPartsLenSnoc(parts[1..], extra);
  }
}

// Join with an empty separator concatenates every part; its length is exactly
// the sum of the parts' lengths, tracked above as `outLen` while building them.
lemma JoinEmptySepLen(parts: seq<string>)
  ensures |Join(parts, "")| == SumPartsLen(parts)
{
  JoinEmptySepLenFrom(parts);
}

ghost function SumPartsLen(parts: seq<string>): nat
{
  if |parts| == 0 then 0 else |parts[0]| + SumPartsLen(parts[1..])
}

lemma JoinEmptySepLenFrom(parts: seq<string>)
  ensures |Join(parts, "")| == SumPartsLen(parts)
  decreases |parts|
{
  if |parts| == 0 {
  } else {
    JoinEmptySepLenFrom(parts[1..]);
    assert Join(parts, "") == parts[0] + Join(parts[1..], "");
  }
}

method Solve(n: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 401 * |s| + 502
{
  steps := 1;
  var cur := s;
  var i := 100;
  while i >= 1
    invariant 0 <= i <= 100
    invariant |cur| <= |s|
    invariant steps <= 1 + (100 - i) * (4 * |s| + 5)
    decreases i
  {
    var pat := "o" + RepeatGo(i);
    RepeatGoLen(i);
    assert |pat| == 1 + 2 * i;
    ghost var repSteps;
    cur, repSteps := ReplaceAll(cur, pat, "***");
    steps := steps + repSteps + 2;
    i := i - 1;
  }
  output := cur + "\n";
  steps := steps + 1;
}
