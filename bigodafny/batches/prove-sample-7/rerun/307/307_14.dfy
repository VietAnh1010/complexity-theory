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

include "../../../../prelude.dfy"
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
  if i > 0 { RepeatGoLen(i - 1); }
}

method ReplaceAll(s: string, pat: string, rep: string) returns (res: string, ghost steps: nat)
  requires |pat| > 0
  requires |pat| <= 201
  requires |rep| <= |pat|
  ensures |res| <= |s|
  ensures steps <= 6 * |s| + 3
{
  steps := 1;
  var parts: seq<string> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |Join(parts, "")| <= i
    invariant steps <= 1 + 6 * i
    decreases |s| - i
  {
    if i + |pat| <= |s| && s[i..i+|pat|] == pat {
      JoinSplitEmptySep(parts, [rep]);
      parts := parts + [rep];
      i := i + |pat|;
    } else {
      JoinSplitEmptySep(parts, [[s[i]]]);
      parts := parts + [[s[i]]];
      i := i + 1;
    }
    steps := steps + 6;
  }
  res := Join(parts, "");
  steps := steps + 2;
}

method Solve(n: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 800 * |s| + 2200
{
  steps := 1;
  var cur := s;
  var i := 100;
  var t := 0;
  var B := 7 * |s| + 20;
  while i >= 1
    invariant 0 <= i <= 100
    invariant t == 100 - i
    invariant |cur| <= |s|
    invariant steps <= 1 + t * B
    decreases i
  {
    RepeatGoLen(i);
    var pat := "o" + RepeatGo(i);
    var rep := "***";
    var res, repSteps := ReplaceAll(cur, pat, rep);
    CostMulDistrib(t, 1, t + 1, B);
    steps := steps + repSteps + 8;
    cur := res;
    t := t + 1;
    i := i - 1;
  }
  output := cur + "\n";
  steps := steps + 1;
}
