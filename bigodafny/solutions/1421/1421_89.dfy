// p02899 AtCoder Beginner Contest 142 - Go to School  (problem 1421, solution 1421_89)
// time complexity: O(nlogn)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = map(int, input().split())
// 
// for i, x in sorted(enumerate(a), key=lambda x:x[1]):
// 	print(i+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var pairs := seq(|a_list|, i requires 0 <= i < |a_list| => (a_list[i], i));
  var srt := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  var vals := seq(|srt|, i requires 0 <= i < |srt| => srt[i].1 + 1);
  if |vals| == 0 {
    output := "";
  } else {
    output := JoinInts(vals, "\n") + "\n";
  }
}
