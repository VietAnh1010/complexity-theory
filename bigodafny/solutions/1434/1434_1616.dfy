// 228_A. Is your horseshoe on the other hoof?  (problem 1434, solution 1434_1616)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = list(map(int,input().split()))
// count = 0
// 
// for i in range(1,len(a)):
// 	if a[i] in a[:i]:
// 		count += 1
// print(count)	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsInt1434a(xs: seq<int>, v: int): bool
  decreases |xs|
{
  if |xs| == 0 then false
  else if xs[0] == v then true
  else ContainsInt1434a(xs[1..], v)
}

method Solve(values: seq<int>) returns (output: string)
{
  var count := 0;
  var i := 1;
  while i < |values|
    decreases |values| - i
  {
    if ContainsInt1434a(values[..i], values[i]) { count := count + 1; }
    i := i + 1;
  }
  output := IntToString(count);
}
