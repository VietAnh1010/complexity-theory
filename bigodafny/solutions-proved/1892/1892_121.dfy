// 1149_A. Prefix Sum Primes  (problem 1892, solution 1892_121)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=list(map(int,input().split()))
// flag1=0
// flag2=0
// for i in range(n):
// 	if l[i]==2:
// 		flag1=1
// 		break
// for i in range(n):
// 	if l[i]==1:
// 		flag2=1
// 		break
// if flag1==0 or flag2==0:
// 	print(*l)
// else:
// 	print(2,1,end=' ')
// 	l.remove(2)
// 	l.remove(1)
// 	l.sort(reverse=True)
// 	print(*l)
// --------------------------------------------------------------------

// PROOF NOTE (relation: confirms).
// Two flag scans with early exit, then either one JoinInts or two RemoveFirst
// passes, a sort and a JoinInts. The sort is on at most |a_list| elements and
// folds into NLogN(|a_list|) by the prelude's SortCostWithin; everything else
// is linear. JoinInts is charged one step per number, per the IntToString
// convention.

include "../../prelude.dfy"
import opened Prelude

function RemoveFirst(l: seq<int>, x: int): seq<int>
  decreases |l|
{
  if |l| == 0 then []
  else if l[0] == x then l[1..]
  else [l[0]] + RemoveFirst(l[1..], x)
}

lemma RemoveFirstLen(l: seq<int>, x: int)
  ensures |RemoveFirst(l, x)| <= |l|
  decreases |l|
{
  if |l| > 0 && l[0] != x { RemoveFirstLen(l[1..], x); }
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n <= |a_list|
  ensures steps <= 2 * NLogN(|a_list|) + 7 * |a_list| + 6
{
  ghost var N := |a_list|;
  steps := 1;
  var l := a_list;
  var flag1 := false;
  var flag2 := false;
  var i := 0;
  while i < n && !flag1
    invariant 0 <= i <= N
    invariant steps == 1 + 2 * i
    decreases !flag1, n - i
  {
    if l[i] == 2 { flag1 := true; }
    i := i + 1;
    steps := steps + 2;
  }
  ghost var s1 := steps;
  i := 0;
  while i < n && !flag2
    invariant 0 <= i <= N
    invariant steps == s1 + 2 * i
    decreases !flag2, n - i
  {
    if l[i] == 1 { flag2 := true; }
    i := i + 1;
    steps := steps + 2;
  }
  if !flag1 || !flag2 {
    // JoinInts over N numbers: IntToString and its length are charged 1 each
    output := JoinInts(l, " ");
    steps := steps + N + 1;
  } else {
    // RemoveFirst is a recursive helper over the sequence: charged its length
    var rest := RemoveFirst(l, 2);
    RemoveFirstLen(l, 2);
    steps := steps + N;
    ghost var r1 := |rest|;
    rest := RemoveFirst(rest, 1);
    RemoveFirstLen(RemoveFirst(l, 2), 1);
    steps := steps + r1;
    assert |rest| <= N;
    steps := steps + SortCost(|rest|);
    SortCostWithin(|rest|, N);
    var descending := Sort(rest, (x: int, y: int) => x > y);
    output := "2 1 " + JoinInts(descending, " ");
    steps := steps + |descending| + 2;
  }
}
