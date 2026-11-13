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

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 10 * |a_list| + 3 + |output|
{
  steps := 1;
  var score: map<int, int> := map[];
  var sup := -2147483648;
  var winner := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps <= 10 * i + 1
    decreases |a_list| - i
  {
    steps := steps + 10;
    var v := a_list[i];
    score := score[v := if v in score then score[v] + 1 else 1];
    if score[v] > sup {
      sup := score[v];
      winner := v;
    }
    i := i + 1;
  }
  output := IntToString(winner);
  IntToStringDigits(winner);
  steps := steps + Digits(winner) + 1;
}
