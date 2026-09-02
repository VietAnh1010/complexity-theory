// 1208_B. Uniqueness  (problem 2650, solution 2650_140)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// data = list(map(int, input().split(' ')))
// seq = sorted(data)
// seq2 = []
// for i in range(0, len(seq)):
//     if (i == 0) or (seq[i-1] != seq[i]):
//         seq2.append(seq[i])
// for i in range(0, len(data)):
//     l = 0
//     r = len(seq2)
//     while r-l > 1:
//         mid = (r+l)//2
//         if (seq2[mid] < data[i]):
//             l = mid + 1
//         elif (seq2[mid] == data[i]):
//             l = mid
//         else:
//             r = mid
//     data[i] = l
// ans = int(1e9)
// pref = 0
// used = list()
// for x in range(n):
//     used.append(0)
// while pref <= n:
//     if pref > 0:
//         if used[data[pref-1]] > 0:
//             break
//         used[data[pref-1]] += 1
//     dused = used.copy()
//     suf = 0
//     while suf < n:
//         ind = data[n - 1 - suf]
//         if dused[ind] > 0:
//             break
//         dused[ind] += 1
//         suf += 1
//     ans = min(ans, n - pref - suf)
//     pref += 1
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

method RankOf(seq2: seq<int>, v: int) returns (rank: int)
  requires |seq2| > 0
  ensures 0 <= rank <= |seq2|
{
  var l := 0;
  var r := |seq2|;
  while r - l > 1
    invariant 0 <= l <= r <= |seq2|
    decreases r - l
  {
    var mid := (r + l) / 2;
    if seq2[mid] < v {
      l := mid + 1;
    } else if seq2[mid] == v {
      l := mid;
    } else {
      r := mid;
    }
  }
  rank := l;
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  requires n >= 1
{
  SortLength(a_list, (x: int, y: int) => x < y);
  var sorted_ := SortInts(a_list);
  var seq2: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |sorted_| == n
    invariant i >= 1 ==> |seq2| >= 1
    decreases n - i
  {
    if i == 0 || sorted_[i - 1] != sorted_[i] {
      seq2 := seq2 + [sorted_[i]];
    }
    i := i + 1;
  }
  assert |seq2| >= 1;
  var data := a_list;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |data| == n
    invariant |seq2| > 0
    invariant forall kk :: 0 <= kk < i ==> 0 <= data[kk] < |seq2|
    decreases n - i
  {
    var rk := RankOf(seq2, data[i]);
    if rk >= |seq2| { rk := |seq2| - 1; }
    data := data[i := rk];
    i := i + 1;
  }
  assert forall kk :: 0 <= kk < n ==> 0 <= data[kk] < |seq2|;
  var ans := 1000000000;
  var pref := 0;
  var used := seq(n, _ => 0);
  while pref <= n
    invariant 0 <= pref
    invariant |used| == n
    invariant |data| == n
    decreases n - pref + 1
  {
    var brk := false;
    if pref > 0 {
      var idxp := data[pref - 1];
      if 0 <= idxp < n && used[idxp] > 0 {
        brk := true;
      } else if 0 <= idxp < n {
        used := used[idxp := used[idxp] + 1];
      }
    }
    if brk {
      pref := n + 1;
    } else {
      var dused := used;
      var suf := 0;
      var k := 0;
      var brk2 := false;
      while k < n && !brk2
        invariant 0 <= suf <= k <= n
        invariant |dused| == n
        decreases n - k
      {
        var ind := data[n - 1 - k];
        if 0 <= ind < n && dused[ind] > 0 {
          brk2 := true;
          k := n;
        } else if 0 <= ind < n {
          dused := dused[ind := dused[ind] + 1];
          suf := suf + 1;
          k := k + 1;
        } else {
          suf := suf + 1;
          k := k + 1;
        }
      }
      var cand := n - pref - suf;
      if cand < ans { ans := cand; }
      pref := pref + 1;
    }
  }
  output := IntToString(ans);
}
