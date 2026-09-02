// 546_B. Soldier and Badges  (problem 2586, solution 2586_216)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// ans=0
// s=sorted(list(map(int,input().split())))
// for i in range(1,n):
//     if s[i]<=s[i-1]:
//         ans+=s[i-1]-s[i]+1
//         s[i]=s[i-1]+1
// print(ans)
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

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  requires n >= 1
{
  SortLength(a_list, (x: int, y: int) => x < y);
  var s := SortInts(a_list);
  var ans := 0;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |s| == n
    decreases n - i
  {
    if s[i] <= s[i - 1] {
      ans := ans + s[i - 1] - s[i] + 1;
      s := s[i := s[i - 1] + 1];
    }
    i := i + 1;
  }
  output := IntToString(ans);
}
