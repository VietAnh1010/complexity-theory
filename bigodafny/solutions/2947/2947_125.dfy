// 637_A. Voting for Photos  (problem 2947, solution 2947_125)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(x) for x in input().split()]
// score = dict()
// sup, winner = -2**31, None
// for v in a:
//     score[v] = score[v] + 1 if v in score else 1
//     if score[v] > sup:
//         sup, winner = score[v], v
// print(winner)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var keys: seq<int> := [];
  var vals: seq<int> := [];
  var sup := -2147483648;
  var winner := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant |keys| == |vals|
    decreases |a_list| - i
  {
    var v := a_list[i];
    var idx := -1;
    var p := 0;
    while p < |keys|
      invariant 0 <= p <= |keys|
      invariant idx == -1 || (0 <= idx < p && keys[idx] == v)
      decreases |keys| - p
    {
      if keys[p] == v { idx := p; }
      p := p + 1;
    }
    if idx == -1 {
      keys := keys + [v];
      vals := vals + [1];
      idx := |keys| - 1;
    } else {
      vals := vals[idx := vals[idx] + 1];
    }
    if 0 <= idx < |vals| && vals[idx] > sup {
      sup := vals[idx];
      winner := v;
    }
    i := i + 1;
  }
  output := IntToString(winner);
}
