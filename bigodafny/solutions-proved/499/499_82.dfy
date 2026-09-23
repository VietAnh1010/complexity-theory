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
  ensures steps <= 2 * NLogN(n) + 9 * n + 11
{
  SortCostNLogN(n);
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
  assert steps <= 2 * NLogN(n) + 9 * n + 11;
  output := IntToString(ans) + "\n";
}
