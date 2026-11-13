include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string, ghost steps: nat)
  requires |s1| > 0 && |s2| > 0
  ensures steps <= 2 * NLogN(|s1|) + 2 * NLogN(|s2|) + 13 * (|s1| + |s2|) + 5
{
  var n1 := Norm1628a(s1);
  var n2 := Norm1628a(s2);
  NormCostBound(s1);
  NormCostBound(s2);
  NormLen(s1);
  NormLen(s2);
  steps := NormCost(s1) + NormCost(s2) + |n1| + |n2| + 2;
  if n1 == n2 {
    output := "YES";
  } else {
    output := "NO";
  }
}

function Norm1628a(s: string): string
  requires |s| > 0
  ensures |Norm1628a(s)| == |s|
  decreases |s|
{
  if |s| % 2 == 1 then s
  else
    var half := |s| / 2;
    var a := Norm1628a(s[..half]);
    var b := Norm1628a(s[half..]);
    if StringLess(a, b) then a + b else b + a
}

// ghost cost: |s|, %, two slices, StringLess <= half + 1, concat <= half, constants
ghost function NormCost(s: string): nat
  requires |s| > 0
  decreases |s|
{
  if |s| % 2 == 1 then 2
  else NormCost(s[..|s| / 2]) + NormCost(s[|s| / 2..]) + 2 * |s| + 8
}

lemma NormLen(s: string)
  requires |s| > 0
  ensures |Norm1628a(s)| == |s|
{
}

lemma NLogNDouble(m: nat)
  requires m >= 1
  ensures NLogN(2 * m) == 2 * NLogN(m) + 2 * m
{
  reveal NLogN();
  assert (2 * m + 1) / 2 == m;
  assert CeilLog2(2 * m) == 1 + CeilLog2(m);
  CostMulDistrib(2, m, 1, 0);
}

lemma NLogNGe(k: nat)
  requires k >= 1
  ensures NLogN(k) >= k
{
  reveal NLogN();
}

lemma NormCostBound(s: string)
  requires |s| > 0
  ensures NormCost(s) + 8 <= 2 * NLogN(|s|) + 12 * |s|
  decreases |s|
{
  if |s| % 2 == 1 {
    NLogNGe(|s|);
  } else {
    var m := |s| / 2;
    NormCostBound(s[..m]);
    NormCostBound(s[m..]);
    NLogNDouble(m);
  }
}
