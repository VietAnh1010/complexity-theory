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

method Solve(n: int, k: int, m: int, s: string) returns (output: string)
{

  var a := k;
  var b := m;
  var tot := a + b;
  var pieces := SplitChar(s, '*');
  var i := 0;
  while i < |pieces|
    invariant 0 <= i <= |pieces|
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
  }
  output := IntToString(tot - a - b);
}


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
