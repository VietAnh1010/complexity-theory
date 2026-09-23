// 962_B. Students in Railway Carriage  (problem 566, solution 566_183)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, a, b = list(map(int, input().split()))
// row = sorted([_ for _ in input().split('*') if _], key=lambda x: len(x), reverse=True)
//
// total = 0
// for _ in row:
// 	if a == 0 and b == 0:
// 		break
// 	l = len(_)
// 	odd, even = l // 2 + l % 2, l // 2
// 	if a > b:
// 		da = min(odd, a)
// 		db = min(even, b)
// 		total += da + db
// 		a -= da
// 		b -= db
// 	else:
// 		da = min(even, a)
// 		db = min(odd, b)
// 		total += da + db
// 		a -= da
// 		b -= db
//
// print(total)
// --------------------------------------------------------------------
//
// PROOF NOTE (relation: confirms). Sort(lens, LessInt) costs
// SortCost(|pieces|), bounded by the prelude's SortCostWithin in terms of
// |s| + 1, the tight recursion-tree argument, so the proved bound is
// O(n log n). SplitChar is charged flat at |s|,
// matching COMPLEXITY.md's rule for a recursive helper over a string.

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

lemma SplitCharFromLen(s: string, sep: char, i: int, cur: string, acc: seq<string>)
  requires 0 <= i <= |s|
  ensures |SplitCharFrom(s, sep, i, cur, acc)| <= |s| - i + 1 + |acc|
  decreases |s| - i
{
  if i >= |s| {
  } else if s[i] == sep {
    SplitCharFromLen(s, sep, i + 1, "", acc + [cur]);
  } else {
    SplitCharFromLen(s, sep, i + 1, cur + [s[i]], acc);
  }
}

method Solve(n: int, k: int, m: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|s| + 1) + 1 + 10 * (|s| + 1) + 20
{

  var a := k;
  var b := m;
  var pieces := SplitChar(s, '*');
  SplitCharFromLen(s, '*', 0, "", []);
  assert |pieces| <= |s| + 1;
  ghost var steps1: nat := |s| + 1;   // SplitChar: recursive helper over a string, charged its length
  var lens := seq(|pieces|, idx requires 0 <= idx < |pieces| => |pieces[idx]|);
  steps1 := steps1 + |pieces|;
  SortCostWithin(|pieces|, |s| + 1);
  var row := Sort(lens, LessInt);
  SortLength(lens, LessInt);
  assert |row| <= |s| + 1;
  steps1 := steps1 + SortCost(|pieces|);
  var total := 0;
  var i := 0;
  steps := steps1 + 5;
  while i < |row|
    invariant 0 <= i <= |row|
    invariant |row| <= |s| + 1
    invariant steps <= steps1 + 5 + 6 * i
    decreases |row| - i
  {
    var l := row[i];
    var odd := l / 2 + l % 2;
    var even := l / 2;
    if a > b {
      var da := Min(odd, a);
      var db := Min(even, b);
      total := total + da + db;
      a := a - da;
      b := b - db;
    } else {
      var da := Min(even, a);
      var db := Min(odd, b);
      total := total + da + db;
      a := a - da;
      b := b - db;
    }
    i := i + 1;
    steps := steps + 6;
  }
  output := IntToString(total);
  steps := steps + 1;
}


function Min(x: int, y: int): int { if x < y then x else y }

function LessInt(x: int, y: int): bool { x > y }

function SplitChar(s: string, sep: char): seq<string>
{
  SplitCharFrom(s, sep, 0, "", [])
}

function SplitCharFrom(s: string, sep: char, i: int, cur: string, acc: seq<string>): seq<string>
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| then acc + [cur]
  else if s[i] == sep then SplitCharFrom(s, sep, i + 1, "", acc + [cur])
  else SplitCharFrom(s, sep, i + 1, cur + [s[i]], acc)
}
