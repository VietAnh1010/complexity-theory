// --- Python ---------------------------------------------------------
// def solve():
//     n=int(input())
//     s=sorted(input(), key=(lambda x: ord(x)))
//     ind=[[s[0],1]]
//     if len(s) % n!=0:
//         print(-1)
//         return
//     for i in range(1,len(s)):
//         if s[i]!=ind[len(ind)-1][0]:
//             ind.append([s[i],1])
//         else: ind[len(ind)-1][1]+=1
//     ans=[]
//     for ii in ind:
//         if ii[1] % n!=0:
//             print(-1)
//             return
//         ans.extend([ii[0] for i in range(ii[1]//n)])
//     print("".join(ans * n))
// solve()
//
//
//
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

ghost function SumC(g: seq<(char, int)>): int
  decreases |g|
{
  if |g| == 0 then 0 else SumC(g[..|g| - 1]) + g[|g| - 1].1
}

lemma SumCSnoc(g: seq<(char, int)>, x: (char, int))
  ensures SumC(g + [x]) == SumC(g) + x.1
{
  assert (g + [x])[..|g|] == g;
}

lemma LenLeSumC(g: seq<(char, int)>)
  requires forall k :: 0 <= k < |g| ==> g[k].1 >= 1
  ensures |g| <= SumC(g)
  decreases |g|
{
  if |g| > 0 {
    LenLeSumC(g[..|g| - 1]);
  }
}

lemma DivLe(a: int, b: int)
  requires a >= 0 && b >= 1
  ensures a / b <= a
{
}

lemma RepeatLen(s: string, n: nat)
  ensures |Repeat(s, n)| == |s| * n
  decreases n
{
  if n > 0 { RepeatLen(s, n - 1); }
}

method Solve(v_0: int, v_1: string)
    returns (output: string, ghost steps: nat)
  requires 1 <= v_0 <= 1000
  ensures steps <= 2 * NLogN(|v_1|) + 45 * |v_1| + 10 + |output|
{
  steps := 0;
  steps := steps + SortCost(|v_1|);
  var sorted := Sort(v_1, (a: char, b: char) => a < b);
  steps := steps + 1;
  SortCostWithin(|v_1|, |v_1|);
  assert |sorted| == |v_1|;
  var len := |sorted|;
  steps := steps + 2;
  if len % v_0 != 0 {
    output := "-1";
  } else {
    var groups: seq<(char, int)> := [];
    var i := 0;
    while i < len
      invariant 0 <= i <= len
      invariant forall k :: 0 <= k < |groups| ==> groups[k].1 >= 1
      invariant SumC(groups) == i
      invariant steps <= SortCost(|v_1|) + 3 + 24 * i
      decreases len - i
    {
      steps := steps + 2;
      steps := steps + 1;
      var c := sorted[i];
      steps := steps + (3 + if |groups| > 0 then 5 else 0);
      if |groups| > 0 && groups[|groups| - 1].0 == c {
        steps := steps + 3;
        var last := groups[|groups| - 1];
        steps := steps + (7 + |[(c, last.1 + 1)]|);
        assert groups == groups[..|groups| - 1] + [last];
        SumCSnoc(groups[..|groups| - 1], last);
        SumCSnoc(groups[..|groups| - 1], (c, last.1 + 1));
        groups := groups[..|groups| - 1] + [(c, last.1 + 1)];
      } else {
        steps := steps + (2 + |[(c, 1)]|);
        SumCSnoc(groups, (c, 1));
        groups := groups + [(c, 1)];
      }
      steps := steps + 1;
      i := i + 1;
    }
    steps := steps + 1;
    LenLeSumC(groups);
    var ok := true;
    var ans: string := "";
    var j := 0;
    ghost var cnt: int := 0;
    while j < |groups|
      invariant 0 <= j <= |groups|
      invariant forall k :: 0 <= k < |groups| ==> groups[k].1 >= 1
      invariant cnt == SumC(groups[..j])
      invariant steps <= SortCost(|v_1|) + 4 + 24 * len + 13 * j + 2 * cnt
      decreases |groups| - j
    {
      steps := steps + 3;
      steps := steps + 1;
      var pr := groups[j];
      DivLe(pr.1, v_0);
      RepeatLen([pr.0], pr.1 / v_0);
      assert groups[..j + 1] == groups[..j] + [pr];
      SumCSnoc(groups[..j], pr);
      cnt := cnt + pr.1;
      if ok {
        steps := steps + 3;
        if pr.1 % v_0 != 0 {
          ok := false;
        } else {
          steps := steps + (4 + |[pr.0]| * (pr.1 / v_0) + |Repeat([pr.0], pr.1 / v_0)|);
          ans := ans + Repeat([pr.0], pr.1 / v_0);
        }
      }
      steps := steps + 1;
      j := j + 1;
    }
    assert groups[..j] == groups;
    steps := steps + 2;
    steps := steps + 1;
    if !ok {
      output := "-1";
    } else {
      steps := steps + |ans| * v_0;
      RepeatLen(ans, v_0);
      output := Repeat(ans, v_0);
    }
  }
}

import opened Prelude
