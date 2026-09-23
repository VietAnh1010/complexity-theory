// 962_B. Students in Railway Carriage  (problem 566, solution 566_101)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, a, b = map(int, input().split(' '))
// tot = a + b
// lens = [len(s) for s in input().split('*')]
//
// for l in lens:
//     if a > b:
//         if l % 2 == 1:
//             a -= min(a, (l+1)//2)
//         else:
//             a -= min(a, l//2)
//         b -= min(b, l//2)
//     else:
//         a -= min(a, l//2)
//         if l % 2 == 1:
//             b -= min(b, (l+1)//2)
//         else:
//             b -= min(b, l//2)
//
// print(tot - a - b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Min(x: int, y: int): int { if x < y then x else y }

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

// SplitCharFrom is a recursive helper walking the string one character at a
// time; the charge table treats a recursive walk over a seq/string as costing
// its length. This bounds the piece count the outer loop then iterates over.
lemma SplitCharFromLen(s: string, sep: char, i: int, cur: string, acc: seq<string>)
  requires 0 <= i <= |s|
  ensures |SplitCharFrom(s, sep, i, cur, acc)| <= |acc| + (|s| - i) + 1
  decreases |s| - i
{
  if i >= |s| {
  } else if s[i] == sep {
    SplitCharFromLen(s, sep, i + 1, "", acc + [cur]);
  } else {
    SplitCharFromLen(s, sep, i + 1, cur + [s[i]], acc);
  }
}

lemma SplitCharLen(s: string, sep: char)
  ensures |SplitChar(s, sep)| <= |s| + 1
{
  SplitCharFromLen(s, sep, 0, "", []);
}

method Solve(n: int, k: int, m: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 12 * |s| + 20
{
  steps := 1;
  var a := k;
  var b := m;
  var tot := a + b;
  var pieces := SplitChar(s, '*');
  SplitCharLen(s, '*');
  steps := steps + |s| + 3;
  var i := 0;
  while i < |pieces|
    invariant 0 <= i <= |pieces|
    invariant steps <= |s| + 4 + 10 * i
    decreases |pieces| - i
  {
    var l := |pieces[i]|;
    if a > b {
      if l % 2 == 1 {
        a := a - Min(a, (l + 1) / 2);
      } else {
        a := a - Min(a, l / 2);
      }
      b := b - Min(b, l / 2);
    } else {
      a := a - Min(a, l / 2);
      if l % 2 == 1 {
        b := b - Min(b, (l + 1) / 2);
      } else {
        b := b - Min(b, l / 2);
      }
    }
    i := i + 1;
    steps := steps + 10;
  }
  output := IntToString(tot - a - b);
  steps := steps + 2;
}
