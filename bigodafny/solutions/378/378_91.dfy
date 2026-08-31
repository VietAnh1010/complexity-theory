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

method Solve(n: int, pairs: seq<seq<string>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
