// 991_B. Getting an A  (problem 2593, solution 2593_332)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// L = list(map(int, input().split()))
// L = sorted(L)
// s = sum(L)
// c = 0
// p = s/n
// if p >= 4.5:
//     print(0)
// else:
//     for i in range(n):
//         s = s-L[i]+5
//         c += 1
//         if s/n >= 4.5:
//             print(c)
//             break
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
  var l := SortInts(a_list);
  var s := SumSeq(l);
  if 2 * s >= 9 * n {
    output := "0";
  } else {
    var i := 0;
    var res := 0;
    var printed := false;
    while i < n && !printed
      invariant 0 <= i <= n
      invariant |l| == n
      decreases n - i
    {
      s := s - l[i] + 5;
      if 2 * s >= 9 * n {
        res := i + 1;
        printed := true;
      }
      i := i + 1;
    }
    output := IntToString(res);
  }
}
