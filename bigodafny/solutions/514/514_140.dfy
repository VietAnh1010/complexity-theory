// 913_C. Party Lemonade  (problem 514, solution 514_140)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, l = map(int, input().split())
// p = list(map(int, input().split()))
// d = []
// d = [[p[i] / 2**i, i + 1] for i in range(n)]
// d.sort(key = lambda x: x[0])
// res = 10**18
// q = l
// curres = 0
// for i in d:
// 	if i[1] == 1:
// 		curres += p[i[1] - 1] * q
// 		res = min(res, curres)
// 		break
// 	curb = q // 2**(i[1] - 1)
// 	curres += curb * p[i[1] - 1]
// 	res = min(res, curres + p[i[1] - 1])
// 	q %= 2**(i[1] - 1)
// print(res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MergeElemsRI(a: seq<(real, int)>, b: seq<(real, int)>, less: ((real, int), (real, int)) -> bool)
  ensures forall x :: x in Merge(a, b, less) ==> x in a || x in b
  decreases |a| + |b|
{
  if |a| == 0 {
  } else if |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeElemsRI(a, b[1..], less);
  } else {
    MergeElemsRI(a[1..], b, less);
  }
}

lemma SortElemsRI(s: seq<(real, int)>, less: ((real, int), (real, int)) -> bool)
  ensures forall x :: x in Sort(s, less) ==> x in s
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortElemsRI(s[..|s| / 2], less);
    SortElemsRI(s[|s| / 2..], less);
    MergeElemsRI(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

method Solve(n: int, total_score: int, scores: seq<int>) returns (output: string)
  requires n >= 0
  requires |scores| == n
{
  var l := total_score;
  var p := scores;
  var idx := 0;
  var ratios: seq<(real, int)> := [];
  while idx < n
    invariant 0 <= idx <= n
    invariant forall x :: x in ratios ==> 1 <= x.1 <= n
    decreases n - idx
  {
    var r := (p[idx] as real) / (Pow2_140(idx) as real);
    ratios := ratios + [(r, idx + 1)];
    idx := idx + 1;
  }
  var lessFn := (x: (real, int), y: (real, int)) => x.0 < y.0;
  var d := Sort(ratios, lessFn);
  SortElemsRI(ratios, lessFn);
  assert forall x :: x in d ==> 1 <= x.1 <= n;
  var res := 1000000000000000000;
  var q := l;
  var curres := 0;
  var k := 0;
  var doneFlag := false;
  while k < |d| && !doneFlag
    invariant forall x :: x in d ==> 1 <= x.1 <= n
    decreases |d| - k
  {
    var idxPos := d[k].1;
    assert d[k] in d;
    if idxPos == 1 {
      curres := curres + p[idxPos - 1] * q;
      res := if curres < res then curres else res;
      doneFlag := true;
    } else {
      var pw := Pow2_140(idxPos - 1);
      var curb := q / pw;
      curres := curres + curb * p[idxPos - 1];
      var cand := curres + p[idxPos - 1];
      res := if cand < res then cand else res;
      q := q % pw;
    }
    k := k + 1;
  }
  output := IntToString(res) + "\n";
}

function Pow2_140(e: int): int
  requires e >= 0
  ensures Pow2_140(e) >= 1
  decreases e
{
  if e == 0 then 1 else 2 * Pow2_140(e - 1)
}
