// 228_A. Is your horseshoe on the other hoof?  (problem 1434, solution 1434_1729)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// x = list(map(int, input().split()))
// dic ={}
// for each in x:
//     if each not in dic:
//         dic[each] = 0
//     dic[each] += 0
// h = len(dic)
// print(4 - h)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsInt1434b(xs: seq<int>, v: int): bool
  decreases |xs|
{
  if |xs| == 0 then false
  else if xs[0] == v then true
  else ContainsInt1434b(xs[1..], v)
}

function CountDistinct1434(xs: seq<int>): int
  decreases |xs|
{
  if |xs| == 0 then 0
  else if ContainsInt1434b(xs[1..], xs[0]) then CountDistinct1434(xs[1..])
  else 1 + CountDistinct1434(xs[1..])
}

method Solve(values: seq<int>) returns (output: string)
{
  var h := CountDistinct1434(values);
  output := IntToString(4 - h);
}
