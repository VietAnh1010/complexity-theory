// 437_B. The Child and Set  (problem 1827, solution 1827_66)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
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

// PROOF NOTE (relation: confirms).
// n here is l, an input VALUE: the loop runs once per integer 1..l. Per the
// value-versus-size convention the bound is stated in it. Building list1
// calls Lowbit(i), whose recursion depth -- charged as LowbitDepth -- is at
// most SearchPot(i), so the l calls fold into NLogN(l) by the prelude's
// SearchLoopWithin. The sort of the l pairs folds in by SortCostWithin, and
// the greedy pass and the output are linear.

include "../../prelude.dfy"
import opened Prelude

function Lowbit(v: int): int
  requires v >= 1
  decreases v
{
  if v % 2 == 1 then 1 else 2 * Lowbit(v / 2)
}

// The cost of Lowbit(v): its recursion depth, one step per halving. Mirrors
// Lowbit exactly, as SortCost mirrors Sort.
ghost function LowbitDepth(v: int): nat
  requires v >= 1
  decreases v
{
  if v % 2 == 1 then 1 else 1 + LowbitDepth(v / 2)
}

// Lowbit halves an even v, so its depth is at most the halving potential.
lemma LowbitDepthBound(v: int)
  requires v >= 1
  ensures LowbitDepth(v) <= SearchPot(v)
  decreases v
{
  if v % 2 == 0 {
    LowbitDepthBound(v / 2);
    assert (v + 1) / 2 == v / 2;
  }
}

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures var L := if b > 0 then b else 0;
          steps <= 3 * NLogN(L) + 9 * L + 10
{
  var s := a;
  var l := b;
  ghost var L: nat := if l > 0 then l else 0;
  ghost var K: nat := SearchPot(L) + 3;
  steps := 1;
  var list1: seq<(int, int)> := [];
  var i := 1;
  while i <= l
    invariant 1 <= i
    invariant l >= 1 ==> i <= l + 1
    invariant i - 1 <= L
    invariant |list1| == i - 1
    invariant steps <= 1 + (i - 1) * K
    decreases l - i
  {
    LowbitDepthBound(i);
    SearchPotMonotone(i, L);
    steps := steps + LowbitDepth(i) + 3;
    list1 := list1 + [(Lowbit(i), i)];
    i := i + 1;
    CostMulDistrib(i - 2, 1, i - 1, K);
  }
  assert |list1| <= L;
  SearchLoopWithin(|list1|, L, L, 1, 3);
  assert steps <= 1 + NLogN(L) + 3 * L;
  steps := steps + SortCost(|list1|);
  SortCostWithin(|list1|, L);
  var sorted := Sort(list1, (p: (int, int), q: (int, int)) =>
    if p.0 != q.0 then p.0 > q.0 else p.1 > q.1);
  ghost var s2 := steps;
  // l < 1 leaves list1 empty and the next loop never runs.
  assert l >= 1 ==> |sorted| == l;
  var ll: seq<int> := [];
  var k := 0;
  while k < l
    invariant 0 <= k <= L
    invariant l >= 1 ==> |sorted| == l
    invariant |ll| <= k
    invariant steps == s2 + 4 * k
    decreases l - k
  {
    if sorted[k].0 <= s {
      ll := ll + [sorted[k].1];
      s := s - sorted[k].0;
    }
    k := k + 1;
    steps := steps + 4;
  }
  if s == 0 {
    output := IntToString(|ll|) + "\n" + JoinInts(ll, " ");
    steps := steps + |ll| + 4;
  } else {
    output := IntToString(-1);
    steps := steps + 1;
  }
}
