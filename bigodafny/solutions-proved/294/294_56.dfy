// p03687 AtCoder Grand Contest 016 - Shrinking  (problem 294, solution 294_56)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// exitLower = list(set(list(s)))
// m = len(s)
// 
// for alp in exitLower:
//     SL = list(s)
//     cnt = 0
//     while len(set(SL)) > 1:
//         for i in range(len(SL)-1):
//             if SL[i+1] == alp:
//                 SL[i] = alp
//         SL.pop()
//         cnt += 1
//     m = min(m,cnt)
// 
// print(m)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function Tri(k: int): nat
  decreases k
{
  if k <= 0 then 0 else k + Tri(k - 1)
}

lemma TriLe(k: nat)
  ensures Tri(k) <= k * k
{
  if k > 0 {
    TriLe(k - 1);
    assert k * k == (k - 1) * (k - 1) + 2 * k - 1;
  }
}

ghost function {:opaque} ShrinkBound(n: nat): nat
{
  14 * (n * n) + 6 * n + 20
}

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 8 * |s| + 5 + |s| * ShrinkBound(|s|) + |output|
{
  steps := 0;
  var seen: set<char> := {};
  var distinct: seq<char> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |distinct| <= i
    invariant steps == 8 * i
    decreases |s| - i
  {
    if s[i] !in seen {
      seen := seen + {s[i]};
      distinct := distinct + [s[i]];
    }
    i := i + 1;
    steps := steps + 8;
  }
  var m := |s|;
  var k := 0;
  ghost var K := ShrinkBound(|s|);
  steps := steps + 1;
  while k < |distinct|
    invariant 0 <= k <= |distinct|
    invariant steps <= 8 * |s| + 1 + k * K
    decreases |distinct| - k
  {
    var cnt, st := ShrinkCount(s, distinct[k]);
    TriLe(|s|);
    reveal ShrinkBound();
    assert st + 4 <= K;
    if cnt < m { m := cnt; }
    CostMulDistrib(k, 1, k + 1, K);
    k := k + 1;
    steps := steps + st + 4;
  }
  CostMulMonoLeft(|distinct|, |s|, K);
  output := IntToString(m);
  IntToStringDigits(m);
  steps := steps + Digits(m);
}

method AllSameChar(s: string) returns (r: bool, ghost steps: nat)
  ensures !r ==> |s| >= 2
  ensures steps <= 5 * |s| + 2
{
  steps := 2;
  r := true;
  var i := 1;
  while i < |s|
    invariant !r ==> |s| >= 2
    invariant 1 <= i <= |s| || (|s| == 0 && i == 1)
    invariant steps <= 5 * (i - 1) + 2
    decreases |s| - i
  {
    if s[i] != s[0] { r := false; }
    i := i + 1;
    steps := steps + 5;
  }
}

method ShrinkCount(s0: string, alp: char) returns (cnt: int, ghost steps: nat)
  ensures steps <= 14 * Tri(|s0|) + 5 * |s0| + 4
{
  steps := 2;
  var SL := s0;
  cnt := 0;
  var same, st0 := AllSameChar(SL);
  steps := steps + st0;
  while !same
    invariant !same ==> |SL| >= 2
    invariant |SL| <= |s0|
    invariant steps + 14 * Tri(|SL|) <= 14 * Tri(|s0|) + 5 * |s0| + 4
    decreases |SL|
  {
    var tmp: seq<char> := [];
    var i := 0;
    ghost var base := steps;
    while i < |SL| - 1
      invariant 0 <= i <= |SL| - 1
      invariant |tmp| == i
      invariant steps == base + 8 * i
      decreases |SL| - 1 - i
    {
      if SL[i + 1] == alp {
        tmp := tmp + [alp];
      } else {
        tmp := tmp + [SL[i]];
      }
      i := i + 1;
      steps := steps + 8;
    }
    SL := tmp;
    cnt := cnt + 1;
    ghost var st1;
    same, st1 := AllSameChar(SL);
    steps := steps + st1 + 3;
  }
}
