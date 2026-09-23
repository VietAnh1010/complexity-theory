// 219_A. k-String  (problem 1582, solution 1582_118)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

// PROOF NOTE (relation: confirms).
// A sort of the n characters, one run-length pass, then one pass over the
// groups emitting count/k copies of each. The sort folds into NLogN(n) by the
// prelude's SortCostNLogN. The emitting pass costs the sum of the group counts,
// which is n (SumCnt), and the final Repeat builds |ans| * k <= n characters.

include "../../prelude.dfy"
import opened Prelude

ghost function SumCnt(g: seq<(char, int)>): int
  decreases |g|
{
  if |g| == 0 then 0 else SumCnt(g[..|g| - 1]) + g[|g| - 1].1
}

lemma SumCntSnoc(p: seq<(char, int)>, x: (char, int))
  ensures SumCnt(p + [x]) == SumCnt(p) + x.1
{
  assert (p + [x])[..|p|] == p;
}

lemma SumCntPrefix(g: seq<(char, int)>, j: nat)
  requires j < |g|
  ensures SumCnt(g[..j + 1]) == SumCnt(g[..j]) + g[j].1
{
  assert g[..j + 1][..j] == g[..j];
}

lemma SumCntMono(g: seq<(char, int)>, j: nat)
  requires j <= |g|
  requires forall k :: 0 <= k < |g| ==> g[k].1 >= 1
  ensures SumCnt(g[..j]) <= SumCnt(g)
  decreases |g| - j
{
  if j < |g| {
    SumCntPrefix(g, j);
    SumCntMono(g, j + 1);
  } else {
    assert g[..j] == g;
  }
}

lemma RepeatLen(s: string, n: nat)
  ensures |Repeat(s, n)| == |s| * n
  decreases n
{
  if n > 0 { RepeatLen(s, n - 1); }
}

// one group's share: (a + c/v) * v == a * v + c when v divides c
lemma AddShare(a: nat, c: nat, v: nat)
  requires v >= 1
  requires c % v == 0
  ensures (a + c / v) * v == a * v + c
{
  assert (c / v) * v == c;
}

lemma ShareLe(c: nat, v: nat)
  requires v >= 1
  ensures c / v <= c
{
  CostMulMono(c / v, 1, v);
  assert (c / v) * v <= c;
}

method Solve(v_0: int, v_1: string) returns (output: string, ghost steps: nat)
  requires 1 <= v_0 <= 1000
  ensures steps <= 2 * NLogN(|v_1|) + 12 * |v_1| + 10
{
  ghost var L := |v_1|;
  var sorted := Sort(v_1, (a: char, b: char) => a < b);
  steps := 1 + SortCost(L);
  SortCostNLogN(L);
  var len := |sorted|;
  if len % v_0 != 0 {
    output := "-1";
    steps := steps + 1;
  } else {
    var groups: seq<(char,int)> := [];
    var i := 0;
    while i < len
      invariant 0 <= i <= len
      invariant forall k :: 0 <= k < |groups| ==> groups[k].1 >= 1
      invariant SumCnt(groups) == i
      invariant |groups| <= i
      invariant steps == 1 + SortCost(L) + 5 * i
      decreases len - i
    {
      var c := sorted[i];
      if |groups| > 0 && groups[|groups|-1].0 == c {
        var last := groups[|groups|-1];
        ghost var pre := groups[..|groups|-1];
        assert groups == pre + [last];
        SumCntSnoc(pre, last);
        groups := groups[..|groups|-1] + [(c, last.1 + 1)];
        SumCntSnoc(pre, (c, last.1 + 1));
      } else {
        SumCntSnoc(groups, (c, 1));
        groups := groups + [(c, 1)];
      }
      i := i + 1;
      steps := steps + 5;
    }
    ghost var s2 := steps;
    var ok := true;
    var ans: string := "";
    var j := 0;
    while j < |groups|
      invariant 0 <= j <= |groups|
      invariant forall k :: 0 <= k < |groups| ==> groups[k].1 >= 1
      invariant |ans| * v_0 <= SumCnt(groups[..j])
      invariant steps <= s2 + 4 * j + 2 * SumCnt(groups[..j])
      decreases |groups| - j
    {
      var pr := groups[j];
      SumCntPrefix(groups, j);
      if ok {
        if pr.1 % v_0 != 0 {
          ok := false;
        } else {
          RepeatLen([pr.0], pr.1 / v_0);
          AddShare(|ans|, pr.1, v_0);
          ShareLe(pr.1, v_0);
          // Repeat builds pr.1 / v_0 chars, and the concatenation copies them
          steps := steps + 2 * (pr.1 / v_0);
          ans := ans + Repeat([pr.0], pr.1 / v_0);
        }
      }
      j := j + 1;
      steps := steps + 4;
    }
    assert groups[..|groups|] == groups;
    SumCntMono(groups, |groups|);
    assert len == L;
    assert SumCnt(groups) == L;
    assert |groups| <= L;
    assert |ans| * v_0 <= L;
    assert steps <= s2 + 4 * L + 2 * L;
    assert s2 == 1 + SortCost(L) + 5 * L;
    ghost var tail := |ans| * v_0;
    assert tail <= L;
    if !ok {
      output := "-1";
    } else {
      RepeatLen(ans, v_0);
      output := Repeat(ans, v_0);
      steps := steps + tail;
    }
    steps := steps + 1;
  }
}
