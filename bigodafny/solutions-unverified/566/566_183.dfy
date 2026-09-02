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

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, m: int, s: string) returns (output: string)
{

  var a := k;
  var b := m;
  var pieces := SplitChar(s, '*');
  var lens := seq(|pieces|, idx requires 0 <= idx < |pieces| => |pieces[idx]|);
  var row := Sort(lens, LessInt);
  var total := 0;
  var i := 0;
  while i < |row|
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
  }
  output := IntToString(total);
}


function Min(x: int, y: int): int { if x < y then x else y }

function LessInt(x: int, y: int): bool { x > y }

function SplitChar(s: string, sep: char): seq<string>
{
  SplitCharFrom(s, sep, 0, "", [])
}

function SplitCharFrom(s: string, sep: char, i: int, cur: string, acc: seq<string>): seq<string>
  requires 0 <= i <= |s|
{
  if i >= |s| then acc + [cur]
  else if s[i] == sep then SplitCharFrom(s, sep, i + 1, "", acc + [cur])
  else SplitCharFrom(s, sep, i + 1, cur + [s[i]], acc)
}
