// 426_A. Sereja and Mugs  (problem 3070, solution 3070_180)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,s=map(int,input().split())
// l=list(map(int,input().split()))
// l.sort()
// sum1=0
// for i in range(n-1):
// 	sum1+=l[i]
// if sum1<=s:
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
// Prelude.Sort is a plain recursive function (merge sort); it carries no
// ghost step counter (prelude.dfy is off limits), so its cost is charged as
// an opaque-but-defined SortCost mirroring Sort's own split. The bound proved
// here is an honest O(k^2) -- weaker than merge sort's true O(k log k) --
// so relation = looser-slack.
ghost function SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1
  else SortCost(k / 2) + SortCost(k - k / 2) + k
}

lemma SquareSplit(k: nat, L: nat)
  requires 2 * L <= k <= 2 * L + 1
  ensures 2 * L * L + 2 * (k - L) * (k - L) <= k * k + 1
{
  var d := k - 2 * L;
  assert d == 0 || d == 1;
  assert k - L == L + d;
  assert 2 * L * L + 2 * (k - L) * (k - L) == 4 * L * L + 4 * L * d + 2 * d * d;
  assert k == 2 * L + d;
  assert k * k == 4 * L * L + 4 * L * d + d * d;
  assert d * d <= 1;
}

lemma QuadTail(k: nat)
  requires k >= 2
  ensures k * k + k + 3 <= 2 * k * k + 1
{
  assert (k - 2) * (k + 1) >= 0;
}

lemma SortCostBound(k: nat)
  ensures SortCost(k) <= 2 * k * k + 1
  decreases k
{
  if k <= 1 {
  } else {
    var L := k / 2;
    var R := k - L;
    SortCostBound(L);
    SortCostBound(R);
    SquareSplit(k, L);
    assert SortCost(k) == SortCost(L) + SortCost(R) + k;
    assert SortCost(L) + SortCost(R) + k <= (2 * L * L + 1) + (2 * R * R + 1) + k;
    assert (2 * L * L + 1) + (2 * R * R + 1) + k == 2 * L * L + 2 * R * R + k + 2;
    assert 2 * L * L + 2 * R * R + k + 2 <= (k * k + 1) + k + 2;
    QuadTail(k);
  }
}

method Solve(n: int, m: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= SortCost(|a_list|) + 3 * n + 10
{
  steps := 1;
  SortCostBound(|a_list|);
  var l := SortInts(a_list);
  steps := steps + SortCost(|a_list|);
  var sum1 := 0;
  var i := 0;
  steps := steps + 2;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant steps <= SortCost(|a_list|) + 3 * i + 3
    decreases (n - 1) - i
  {
    if i < |l| {
      sum1 := sum1 + l[i];
    }
    i := i + 1;
    steps := steps + 3;
  }
  if sum1 <= m {
    output := "YES";
  } else {
    output := "NO";
  }
  steps := steps + 1;
}
