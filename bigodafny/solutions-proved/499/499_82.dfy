// 1206_B. Make Product Equal One  (problem 499, solution 499_82)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// a.sort()
// ans=0
// for i in range(0,n-1,2):
//     ans+=min(abs(-1-a[i+1])+abs(-1-a[i]),abs(1-a[i+1])+abs(1-a[i]))
// if (n%2==1): ans+=abs(1-a[n-1])
// print(ans)
//     
//     
//     
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound ----------------
// Prelude.Sort/SortInts is a plain recursive function (merge sort); it
// carries no ghost step counter, so its cost is charged as an
// opaque-but-defined SortCost mirroring Sort's own split. The bound proved
// here is an honest O(k^2) -- weaker than merge sort's true O(k log k) -- so
// the row's proved complexity is looser than its O(nlogn) label (looser-slack).
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

lemma MergeLength<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
  ensures |Merge(a, b, less)| == |a| + |b|
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeLength(a, b[1..], less);
  } else {
    MergeLength(a[1..], b, less);
  }
}

lemma SortLength<T>(s: seq<T>, less: (T, T) -> bool)
  ensures |Sort(s, less)| == |s|
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortLength(s[..|s| / 2], less);
    SortLength(s[|s| / 2..], less);
    MergeLength(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

function Abs82(x: int): int
{
  if x < 0 then -x else x
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |a_list| == n
  ensures steps <= 2 * n * n + 9 * n + 11
{
  SortCostBound(n);
  steps := 1 + SortCost(n);
  var a := Sort(a_list, (x: int, y: int) => x < y);
  SortLength(a_list, (x, y) => x < y);
  assert |a| == n;
  var ans := 0;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n + 1
    invariant steps <= 1 + SortCost(n) + 5 * i
    decreases n - 1 - i
  {
    var opt1 := Abs82(-1 - a[i+1]) + Abs82(-1 - a[i]);
    var opt2 := Abs82(1 - a[i+1]) + Abs82(1 - a[i]);
    ans := ans + (if opt1 < opt2 then opt1 else opt2);
    i := i + 2;
    steps := steps + 5;
  }
  assert steps <= 1 + SortCost(n) + 5 * (n + 1);
  if n % 2 == 1 {
    ans := ans + Abs82(1 - a[n-1]);
  }
  steps := steps + 2;
  assert steps <= 2 * n * n + 9 * n + 11;
  output := IntToString(ans) + "\n";
}
