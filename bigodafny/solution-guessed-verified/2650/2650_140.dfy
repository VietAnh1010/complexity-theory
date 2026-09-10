// 2650_140 (problem 2650) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n**2)
//   proved bound    : 50 * n * n + 50 * n + 50
//   proved class    : O(n**2)
//   agent verdict   : proves
//   reference label : O(nlogn)
//   prediction correct against the label: False
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     seq2 built via seq2+[x] in an n-iteration loop (O(n) per append) and
//     rank-loop rewrites data[i:=rk] n times; outer pref-loop runs n+1 times
//     each doing an O(n) dused copy/scan, so multiple independent O(n^2)
//     sources dominate.
//
//   agent notes:
//     Charged seq2+[x] append at its real cost |seq2| (the intended trap).
//     Charged SortInts flatly at n*n+n+5, a loose but sound
//     over-approximation of its true O(n log n) cost, since it's dominated
//     by the loop-driven n^2 term. Charged seq index-update data[i:=x] and
//     plain seq assignment dused:=used as O(1), matching Python list
//     semantics. Needed MulAdd/MulMonoRight/Expand* helper lemmas to isolate
//     multiplications per GUIDE; final combination needed its own lemma to
//     avoid a timeout.
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 2650_140
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
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
// ----------------------------------------------------------------------

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

lemma MulAdd(a: int, x: int, d: int)
  ensures a * (x + d) == a * x + a * d
{}

lemma MulMonoRight(a: int, p: int, q: int)
  requires a >= 0 && p <= q
  ensures a * p <= a * q
{}

lemma ExpandS1(n: int) ensures (n + 5) * n == n * n + 5 * n {}
lemma ExpandS2(n: int) ensures (4 * n + 10) * n == 4 * n * n + 10 * n {}
lemma ExpandS3(n: int) ensures (5 * n + 15) * (n + 1) == 5 * n * n + 20 * n + 15 {}

lemma FinalBound(n: int, sc: int, a: int, b: int, c: int)
  requires n >= 1
  requires sc == n * n + n + 5
  requires a <= n * n + 5 * n + 5
  requires b <= 4 * n * n + 10 * n + 5
  requires c <= 5 * n * n + 20 * n + 30
  ensures sc + a + b + c + 10 <= 50 * n * n + 50 * n + 50
{}

method RankOf(seq2: seq<int>, v: int) returns (rank: int, ghost steps: nat)
  requires |seq2| > 0
  ensures 0 <= rank <= |seq2|
  ensures steps <= 4 * |seq2| + 4
{
  var l := 0;
  var r := |seq2|;
  steps := 1;
  while r - l > 1
    invariant 0 <= l <= r <= |seq2|
    invariant steps <= 4 * (|seq2| - (r - l)) + 1
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
    steps := steps + 4;
  }
  rank := l;
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 50 * n * n + 50 * n + 50
{
  SortLength(a_list, (x: int, y: int) => x < y);
  var sorted_ := SortInts(a_list);
  // SortInts is a merge sort (see prelude.dfy): real cost is O(n log n).
  // Charged flatly here at O(n^2), a sound but loose over-approximation,
  // since the algorithm's own loops below already force an O(n^2) bound.
  ghost var sortCost: nat := n * n + n + 5;

  var seq2: seq<int> := [];
  var i := 0;
  ghost var s1: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |sorted_| == n
    invariant i >= 1 ==> |seq2| >= 1
    invariant |seq2| <= i
    invariant s1 <= (n + 5) * i + 5
    decreases n - i
  {
    if i == 0 || sorted_[i - 1] != sorted_[i] {
      s1 := s1 + |seq2|;
      seq2 := seq2 + [sorted_[i]];
    }
    s1 := s1 + 5;
    MulAdd(n + 5, i, 1);
    i := i + 1;
  }
  assert |seq2| >= 1;
  assert s1 <= (n + 5) * n + 5;

  var data := a_list;
  i := 0;
  ghost var s2: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |data| == n
    invariant |seq2| > 0
    invariant forall kk :: 0 <= kk < i ==> 0 <= data[kk] < |seq2|
    invariant s2 <= (4 * n + 10) * i + 5
    decreases n - i
  {
    var rk, rsteps := RankOf(seq2, data[i]);
    s2 := s2 + rsteps;
    if rk >= |seq2| { rk := |seq2| - 1; }
    data := data[i := rk];
    s2 := s2 + 5;
    MulAdd(4 * n + 10, i, 1);
    i := i + 1;
  }
  assert forall kk :: 0 <= kk < n ==> 0 <= data[kk] < |seq2|;
  assert s2 <= (4 * n + 10) * n + 5;

  var ans := 1000000000;
  var pref := 0;
  var used := seq(n, _ => 0);
  ghost var s3: nat := 0;
  while pref <= n
    invariant 0 <= pref <= n + 1
    invariant |used| == n
    invariant |data| == n
    invariant s3 <= (5 * n + 15) * pref + 15
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
    s3 := s3 + 5;
    if brk {
      MulAdd(5 * n + 15, pref, n + 1 - pref);
      pref := n + 1;
    } else {
      var dused := used;
      var suf := 0;
      var k := 0;
      var brk2 := false;
      ghost var s3inner: nat := 0;
      while k < n && !brk2
        invariant 0 <= suf <= k <= n
        invariant |dused| == n
        invariant s3inner <= 5 * k + 5
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
        s3inner := s3inner + 5;
      }
      assert s3inner <= 5 * n + 5;
      s3 := s3 + s3inner;
      var cand := n - pref - suf;
      if cand < ans { ans := cand; }
      MulAdd(5 * n + 15, pref, 1);
      pref := pref + 1;
    }
  }
  MulMonoRight(5 * n + 15, pref, n + 1);
  assert s3 <= (5 * n + 15) * (n + 1) + 15;

  ExpandS1(n);
  ExpandS2(n);
  ExpandS3(n);
  assert s1 <= n * n + 5 * n + 5;
  assert s2 <= 4 * n * n + 10 * n + 5;
  assert s3 <= 5 * n * n + 20 * n + 30;
  assert sortCost == n * n + n + 5;
  FinalBound(n, sortCost, s1, s2, s3);

  output := IntToString(ans);
  steps := sortCost + s1 + s2 + s3 + 10;
}
