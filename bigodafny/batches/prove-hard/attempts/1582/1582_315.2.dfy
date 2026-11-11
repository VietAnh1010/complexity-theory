// --- Python ---------------------------------------------------------
// from collections import defaultdict
// d=defaultdict(lambda:0)
// k=int(input())
// s=input()
// for i in s:
//     d[i]+=1
//     
// 
// f=1
// restring=""
// for i in range(97,123):
//     if d[chr(i)]:
//         if d[chr(i)]%k==0:
//             restring+=(chr(i)*(d[chr(i)]//k))
//             
//         else:
//             f=0
//             break
//         
// 
// print(restring*k if f else -1)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

lemma PSUpd(s: seq<int>, p: nat, n: nat)
  requires p < |s| && n <= |s|
  ensures PrefixSum(s[p := s[p] + 1], n) == PrefixSum(s, n) + (if p < n then 1 else 0)
  decreases n
{
  if n > 0 { PSUpd(s, p, n - 1); }
}

lemma PSMono(s: seq<int>, a: nat, b: nat)
  requires forall k :: 0 <= k < |s| ==> s[k] >= 0
  requires a <= b <= |s|
  ensures PrefixSum(s, a) <= PrefixSum(s, b)
  decreases b
{
  if a < b { PSMono(s, a, b - 1); }
}

lemma ZeroPS(s: seq<int>, n: nat)
  requires n <= |s|
  requires forall k :: 0 <= k < |s| ==> s[k] == 0
  ensures PrefixSum(s, n) == 0
{
  if n > 0 { ZeroPS(s, n - 1); }
}

lemma RepLen(c: char, n: nat)
  ensures |Repeat([c], n)| == n
{
  if n > 0 { RepLen(c, n - 1); }
}

lemma DivMul(c: int, k: int)
  requires k >= 1 && c >= 0 && c % k == 0
  ensures c / k * k == c
{
  assert c == k * (c / k) + c % k;
}

lemma MulGe(t: nat, k: nat)
  requires k >= 1
  ensures t <= t * k
{
  CostMulMono(t, 1, k);
}

method Solve(v_0: int, v_1: string)
    returns (output: string, ghost steps: nat)
  requires v_0 >= 1
  requires forall k :: 0 <= k < |v_1| ==> 'a' <= v_1[k] <= 'z'
  ensures steps <= 14 * |v_1| + 420
{
  steps := 0;
  steps := steps + 26;
  var counts: seq<int> := seq(26, i => 0);
  ZeroPS(counts, 26);
  var idx := 0;
  while idx < |v_1|
    invariant 0 <= idx <= |v_1|
    invariant |counts| == 26
    invariant forall k :: 0 <= k < 26 ==> counts[k] >= 0
    invariant PrefixSum(counts, 26) == idx
    invariant steps <= 26 + 11 * idx
    decreases |v_1| - idx
  {
    steps := steps + 3;
    steps := steps + 1;
    var c := v_1[idx];
    steps := steps + 3;
    var pos := c as int - 'a' as int;
    steps := steps + 3;
    PSUpd(counts, pos, 26);
    counts := counts[pos := counts[pos] + 1];
    steps := steps + 1;
    idx := idx + 1;
  }
  steps := steps + 2;
  var ok := true;
  var restring: string := "";
  var ci := 0;
  ghost var tot: nat := 0;
  while ci < 26
    invariant 0 <= ci <= 26
    invariant |counts| == 26
    invariant forall k :: 0 <= k < 26 ==> counts[k] >= 0
    invariant PrefixSum(counts, 26) == |v_1|
    invariant |restring| == tot
    invariant tot * v_0 <= PrefixSum(counts, ci)
    invariant steps <= 28 + 11 * |v_1| + 15 * ci + 2 * tot
    decreases 26 - ci
  {
    steps := steps + 2;
    steps := steps + (1 + if ok then 2 else 0);
    if ok && counts[ci] > 0 {
      steps := steps + 3;
      if counts[ci] % v_0 != 0 {
        ok := false;
      } else {
        DivMul(counts[ci], v_0);
        RepLen(('a' as int + ci) as char, counts[ci] / v_0);
        CostMulDistrib(tot, counts[ci] / v_0, tot + counts[ci] / v_0, v_0);
        steps := steps + (6 + |[('a' as int + ci) as char]| * (counts[ci] / v_0) + |Repeat([('a' as int + ci) as char], counts[ci] / v_0)|);
        restring := restring + Repeat([('a' as int + ci) as char], counts[ci] / v_0);
        tot := tot + counts[ci] / v_0;
      }
    }
    steps := steps + 1;
    assert PrefixSum(counts, ci + 1) == PrefixSum(counts, ci) + counts[ci];
    ci := ci + 1;
  }
  steps := steps + 1;
  PSMono(counts, ci, 26);
  MulGe(tot, v_0);
  if ok {
    steps := steps + |restring| * v_0;
    output := Repeat(restring, v_0);
  } else {
    output := "-1";
  }
}

import opened Prelude
