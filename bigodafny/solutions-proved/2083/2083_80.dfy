// 1107_C. Brutality  (problem 2083, solution 2083_80)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// l=list(map(int,input().split()))
// s=str(input())
// t=0
// i=0
// while(i<n):
//     j=i
//     p=[]
//     while(j<n and s[i]==s[j]):
//         p.append(l[j])
//         j+=1
//     p.sort(reverse=True)
//     c=min(k,len(p))
//     t=t+sum(p[0:c])
//     i=j
// print(t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma SortCostByN(m: nat, n: nat)
  requires m <= n
  ensures SortCost(m) <= 2 * m * (CeilLog2(n) + 1) + 1
{
  SortCostTreeBound(m);
  CeilLog2Monotone(m, n);
  MulMonoRight(2 * m, CeilLog2(m) + 1, CeilLog2(n) + 1);
}

lemma MulDistribGeneral(K: nat, x: nat, y: nat)
  ensures K * (x + y) == K * x + K * y
{ }

lemma FinalBound(base1: nat, K: nat, logn: nat, iOld: nat, j: nat, sortCostP: nat, c: nat)
  requires j >= iOld + 1
  requires sortCostP <= 2 * (j - iOld) * (logn + 1) + 1
  requires c <= j - iOld
  requires K == 2 * logn + 12
  ensures base1 + K * iOld + 3 * (j - iOld) + sortCostP + c + 4 <= base1 + K * j
{
  var d := j - iOld;
  assert base1 + K * iOld + 3 * d + sortCostP + c + 4
      <= base1 + K * iOld + 3 * d + (2 * d * (logn + 1) + 1) + d + 4;
  assert 2 * d * (logn + 1) == 2 * d * logn + 2 * d;
  assert 3 * d + (2 * d * logn + 2 * d) + 1 + d + 4 == 2 * d * logn + 6 * d + 5;
  assert 6 * d + 5 <= 12 * d;
  MulDistribGeneral(K, iOld, d);
  assert K * (iOld + d) == K * iOld + K * d;
  assert K * d == 2 * d * logn + 12 * d;
  assert iOld + d == j;
}

method Solve(a: int, b: int, c_list: seq<int>, d: string) returns (output: string, ghost steps: nat)
  requires |c_list| == a
  requires |d| == a
  requires b >= 0
  ensures steps <= (2 * CeilLog2(a) + 12) * a + 3
{
  var n := a;
  var k := b;
  var l := c_list;
  var s := d;
  var t := 0;
  var i := 0;
  ghost var K := 2 * CeilLog2(n) + 12;
  steps := 1;
  ghost var base1 := steps;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= base1 + K * i
    decreases n - i
  {
    ghost var iOld := i;
    var j := i;
    var p: seq<int> := [];
    ghost var base2 := steps;
    while j < n && s[i] == s[j]
      invariant i <= j <= n
      invariant |p| == j - i
      invariant steps <= base2 + 3 * (j - i)
      decreases n - j
    {
      p := p + [l[j]];
      j := j + 1;
      steps := steps + 3;
    }
    assert j >= iOld + 1;
    var sortedDesc := Sort(p, (x: int, y: int) => x > y);
    SortCostByN(|p|, n);
    steps := steps + SortCost(|p|);
    var c := if k < |sortedDesc| then k else |sortedDesc|;
    steps := steps + 1;
    var slice := sortedDesc[0..c];
    steps := steps + 1;
    t := t + SumSeq(slice);
    steps := steps + c + 1;
    i := j;
    steps := steps + 1;
    assert c <= j - iOld;
    assert steps <= base2 + 3 * (j - iOld) + SortCost(|p|) + c + 4;
    assert steps <= base1 + K * iOld + 3 * (j - iOld) + SortCost(|p|) + c + 4;
    FinalBound(base1, K, CeilLog2(n), iOld, j, SortCost(|p|), c);
  }
  output := IntToString(t);
  steps := steps + 1;
}
