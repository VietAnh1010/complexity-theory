// 608_C. Chain Reaction  (problem 2826, solution 2826_42)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// lis=[0]*(1000004)
// dp=[0]*(1000004)
// for i in range(n):
//     a,b = map(int,input().split())
//     lis[a]=b
// if lis[0]>0:
//     dp[0]=1    
// for i in range(1,1000002):
//     if lis[i]>0:
//         dp[i]=dp[max(-1,i-lis[i]-1)]+1
//     else:
//         dp[i]=dp[i-1]        
// print(n-max(dp))        
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// The one `array<T>` left in `solutions/`. `batches/cost-axioms/PLAN.md` § 2
// removed arrays from the corpus in favour of `seq`; this row is its single
// recorded exception, and the exception is measured, not assumed.
//
// The Python allocates a 1_000_004-entry table and fills 1_000_002 of it in a
// loop, each entry reading an earlier one. Under `seq` that is 10^6 rounds of
// `Seq.set`, and `Seq.set` is `l = list(self.Elements); l[key] = value` -- a
// full copy per write, so ~10^12 element copies. Rewritten to `seq` this row
// went from 16s for all 8 tests to exceeding a 60s per-test budget on the
// first one. `dp := dp + [v]` does not rescue it either: `__add__` is an O(1)
// `Concat` rope, but the next `dp[back]` read forces it flat again, so the
// append/read alternation is quadratic too.
//
// Keeping `array` here is a statement about the backend, not about the cost
// model: under the axioms this row's `seq` version and this `array` version
// are charged identically. What the axioms cannot do is make the `seq` version
// finish, and `validate.py` is non-negotiable.

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
{
  var size := 1000004;
  var lis := new int[size];
  var dp := new int[size];
  var z := 0;
  while z < size
    invariant 0 <= z <= size
  {
    lis[z] := 0;
    dp[z] := 0;
    z := z + 1;
  }
  var idx := 0;
  while idx < |pairs|
    invariant 0 <= idx <= |pairs|
  {
    var row := pairs[idx];
    if |row| >= 2 {
      var a := row[0];
      var b := row[1];
      if 0 <= a < size {
        lis[a] := b;
      }
    }
    idx := idx + 1;
  }
  if lis[0] > 0 {
    dp[0] := 1;
  }
  var i := 1;
  while i < 1000002
    invariant 1 <= i <= 1000002
  {
    if lis[i] > 0 {
      var back := i - lis[i] - 1;
      if back >= 0 && back < i {
        dp[i] := dp[back] + 1;
      } else {
        dp[i] := 0 + 1;
      }
    } else {
      dp[i] := dp[i-1];
    }
    i := i + 1;
  }
  var best := 0;
  var k := 0;
  while k < size
    invariant 0 <= k <= size
  {
    if dp[k] > best { best := dp[k]; }
    k := k + 1;
  }
  output := IntToString(n - best);
}
