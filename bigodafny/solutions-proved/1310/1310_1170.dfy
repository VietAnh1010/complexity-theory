// 116_A. Tram  (problem 1310, solution 1310_1170)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// number_of_stations = input()
// people = 0
// max_people= 0
// for i in range(int(number_of_stations)):
//     a_b = input()
//     a, b = a_b.split()
//     a, b = int(a), int(b)
//     people = people + b - a
//     max_people = max(people, max_people)
// print(max_people)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n <= |edges|
  requires forall k :: 0 <= k < |edges| ==> |edges[k]| >= 2
  ensures steps <= 10 * (if n > 0 then n else 0) + 1 + |output|
{
{
  steps := 0;

  var people := 0;
  var maxPeople := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= (if n > 0 then n else 0)
    invariant steps == 10 * i
    decreases n - i
  {
    var aa := edges[i][0];
    var bb := edges[i][1];
    people := people + bb - aa;
    if people > maxPeople { maxPeople := people; }
    i := i + 1;
    steps := steps + 10;
  }
  output := IntToString(maxPeople);
  IntToStringDigits(maxPeople);
  steps := steps + Digits(maxPeople);
}
}
