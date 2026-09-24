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

include "../../../../prelude.dfy"
import opened Prelude

// SplitCharFrom consumes one character of s per recursive call, so the number
// of pieces it can produce is bounded by the number of characters left plus
// the one piece already carried in acc.
lemma SplitCharFromCount(s: string, sep: char, i: int, cur: string, acc: seq<string>)
  requires 0 <= i <= |s|
  ensures |SplitCharFrom(s, sep, i, cur, acc)| <= |acc| + (|s| - i) + 1
  decreases |s| - i
{
  if i < |s| {
    if s[i] == sep {
      SplitCharFromCount(s, sep, i + 1, "", acc + [cur]);
    } else {
      SplitCharFromCount(s, sep, i + 1, cur + [s[i]], acc);
    }
  }
}

lemma SplitCharCount(s: string, sep: char)
  ensures |SplitChar(s, sep)| <= |s| + 1
{
  SplitCharFromCount(s, sep, 0, "", []);
}

method Solve(n: int, k: int, m: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|s| + 1) + 20 * (|s| + 1) + 40
{
  steps := 1;
  var a := k;
  var b := m;
  var pieces := SplitChar(s, '*');
  steps := steps + (|s| + 1);
  SplitCharCount(s, '*');
  var lens := seq(|pieces|, idx requires 0 <= idx < |pieces| => |pieces[idx]|);
  steps := steps + |pieces|;
  var row := Sort(lens, LessInt);
  steps := steps + SortCost(|lens|);
  SortCostWithin(|lens|, |s| + 1);
  assert |row| <= |s| + 1;
  var total := 0;
  var i := 0;
  while i < |row|
    invariant 0 <= i <= |row|
    invariant steps <= 2 * NLogN(|s| + 1) + 6 * |s| + 10 + 6 * i
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
