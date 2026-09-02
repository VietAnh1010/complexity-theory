// 432_B. Football Kit  (problem 378, solution 378_91)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from sys import stdin
// _data = iter(stdin.read().split('\n'))
// input = lambda: next(_data)
// 
// from collections import Counter
// n = int(input())
// ct = Counter()
// a = [tuple(map(int, input().split())) for _ in range(n)]
// for x, y in a:
//     ct[x] += 1
// buf = []
// for x, y in a:
//     buf.append('{} {}'.format((n - 1) + ct[y],
//                               (n - 1) - ct[y]))
// print('\n'.join(buf))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then -ParseIntFrom(s, 1, 0)
  else ParseIntFrom(s, 0, 0)
}

method Solve(n: int, pairs: seq<seq<string>>) returns (output: string)
{
  var ct: map<int, int> := map[];
  var idx := 0;
  while idx < |pairs|
    decreases |pairs| - idx
  {
    var x := ParseInt(pairs[idx][0]);
    if x in ct {
      ct := ct[x := ct[x] + 1];
    } else {
      ct := ct[x := 1];
    }
    idx := idx + 1;
  }
  var lines: seq<string> := [];
  idx := 0;
  while idx < |pairs|
    decreases |pairs| - idx
  {
    var y := ParseInt(pairs[idx][1]);
    var c := if y in ct then ct[y] else 0;
    lines := lines + [IntToString((n - 1) + c) + " " + IntToString((n - 1) - c)];
    idx := idx + 1;
  }
  output := Join(lines, "\n");
}
