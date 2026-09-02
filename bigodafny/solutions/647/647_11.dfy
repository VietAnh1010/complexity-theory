// 859_C. Pie Rules  (problem 647, solution 647_11)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// X = list(map(int, input().split()))
// 
// ali = [None]*(n+1)
// bob = [None]*(n+1)
// 
// ali[n] = 0
// bob[n] = 0
// 
// for i in range(n-1, -1, -1):
// 	bob[i] = max(bob[i+1], ali[i+1]+X[i])
// 	ali[i] = sum(X[i:n]) - bob[i]
// 	
// #print(ali)
// #print(bob)
// 
// print(ali[0], bob[0], sep=' ')
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 1
  requires |a_list| == n
{
  // total[i] = sum of a_list[i..n-1]
  var total := seq(n + 1, _ => 0);
  var i := n - 1;
  while i >= 0
    invariant -1 <= i <= n - 1
    invariant |total| == n + 1
    decreases i
  {
    total := total[i := total[i+1] + a_list[i]];
    i := i - 1;
  }
  var ali := seq(n + 1, _ => 0);
  var bob := seq(n + 1, _ => 0);
  i := n - 1;
  while i >= 0
    invariant -1 <= i <= n - 1
    invariant |total| == n + 1
    invariant |ali| == n + 1
    invariant |bob| == n + 1
    decreases i
  {
    var bv := if bob[i+1] > ali[i+1] + a_list[i] then bob[i+1] else ali[i+1] + a_list[i];
    bob := bob[i := bv];
    ali := ali[i := total[i] - bv];
    i := i - 1;
  }
  output := IntToString(ali[0]) + " " + IntToString(bob[0]);
}
