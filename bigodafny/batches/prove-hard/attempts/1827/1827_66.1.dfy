// --- Python ---------------------------------------------------------
// s,l=map(int,input().split())
// list1=[]
// for i in range(1,l+1):
//     list1.append((i&-i,i))
//     
// list1.sort(reverse=True)
// ll=[]
// for i in range(l):
//     if(list1[i][0]<=s):
//         ll.append(list1[i][1])
//         s-=list1[i][0]
//         
// if(s==0):
//     print(len(ll))
//     print(*ll)
// else:
//     print(-1)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

function Lowbit(v: int): int
  requires v >= 1
  decreases v
{
  if v % 2 == 1 then
    1
  else
    2 * Lowbit(v / 2)
}

ghost function Lowbit_steps(v: int): nat
  requires v >= 1
  decreases v
{
  3 + if v % 2 == 1 then 0 else 2 + Lowbit_steps(v / 2)
}

lemma LowbitStepsBound(v: int)
  requires v >= 1
  ensures Lowbit_steps(v) <= 5 * CeilLog2(v + 1) + 3
  decreases v
{
  if v % 2 == 0 {
    LowbitStepsBound(v / 2);
    assert CeilLog2(v + 1) == 1 + CeilLog2(v / 2 + 1);
  }
}

lemma CeilLogSucc(n: nat)
  requires n >= 1
  ensures CeilLog2(n + 1) <= CeilLog2(n) + 1
{
  CeilLog2Monotone(n + 1, 2 * n);
  assert CeilLog2(2 * n) == 1 + CeilLog2(n);
}

lemma FoldLoop(m: nat, n: nat, a: nat)
  requires m <= n
  ensures m * (a * (CeilLog2(n) + 1)) <= a * NLogN(n)
{
  if n == 0 {
    assert m == 0;
  } else {
    SearchLoopWithin(m, n, n, a, 0);
  }
}

method Solve(a: int, b: int)
    returns (output: string, ghost steps: nat)
  ensures steps <= 31 * NLogN(if b > 0 then b else 0) + 2 * |output| + 12
{
  ghost var n: nat := if b > 0 then b else 0;
  ghost var c: nat := CeilLog2(n) + 1;
  ghost var K: nat := 14 * c;
  steps := 0;
  var s := a;
  var l := b;
  var list1: seq<(int, int)> := [];
  var i := 1;
  while i <= l
    invariant 1 <= i
    invariant l >= 1 ==> i <= l + 1
    invariant |list1| == i - 1
    invariant i - 1 <= n
    invariant steps <= (i - 1) * K
    decreases l - i
  {
    LowbitStepsBound(i);
    if n >= 1 { CeilLogSucc(n); CeilLog2Monotone(i + 1, n + 1); }
    CostMulDistrib(i - 1, 1, i, K);
    steps := steps + 2;
    steps := steps + (2 + Lowbit_steps(i) + |[(Lowbit(i), i)]|);
    list1 := list1 + [(Lowbit(i), i)];
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  FoldLoop(i - 1, n, 14);
  SortCostWithin(|list1|, n);
  steps := steps + SortCost(|list1|);
  var sorted := Sort(list1, (p: (int, int), q: (int, int)) => if p.0 != q.0 then p.0 > q.0 else p.1 > q.1);
  ghost var base := steps;
  assert l >= 1 ==> |sorted| == l;
  var ll: seq<int> := [];
  var k := 0;
  while k < l
    invariant 0 <= k
    invariant k <= n
    invariant |ll| <= k
    invariant steps <= base + 13 * k
    invariant l >= 1 ==> |sorted| == l
    decreases l - k
  {
    steps := steps + 2;
    steps := steps + 3;
    if sorted[k].0 <= s {
      steps := steps + (3 + |[sorted[k].1]|);
      ll := ll + [sorted[k].1];
      steps := steps + 3;
      s := s - sorted[k].0;
    }
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  steps := steps + 1;
  if s == 0 {
    IntToStringDigits(|ll|);
    if |ll| >= 1 { JoinIntsLen(ll, " "); }
    LinearLeNLogN(n);
    steps := steps + (1 + Digits(|ll|) + |"\n"| + (SumDigits(ll) + |ll|) + |JoinInts(ll, " ")|);
    output := IntToString(|ll|) + "\n" + JoinInts(ll, " ");
    assert |output| == Digits(|ll|) + 1 + |JoinInts(ll, " ")|;
    assert SumDigits(ll) <= |JoinInts(ll, " ")|;
  } else {
    IntToStringDigits(-1);
    LinearLeNLogN(n);
    steps := steps + Digits(-1);
    output := IntToString(-1);
  }
}

import opened Prelude
