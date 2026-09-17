// 18_D. Seller Bob  (problem 2942, solution 2942_42)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// d = [0 for i in range(2009)]
// ans = 0
// for i in range(n):
//   s = input().split()
//   x = int(s[1])
//   if s[0] == 'win':
//     d[x] = ans+ 2**x
//   else:
//     ans = max(d[x], ans)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Not a value-vs-size case (batches/prove-sample/PROMPT_convention.md):
// m = |d| = 2009 is a literal baked into the source, not an input size, so
// the outer loop's real cost is 34 per iteration plus <= 2*2008 for the
// inner power loop -- O(n), and 2009 only enters as a fixed constant. The
// actual blocker was n's unconstrained sign: a plain `i <= n` invariant
// fails to establish at i = 0 when n < 0, so the guard is the same
// `i > 0 ==> i <= n` form solutions-proved/2012/2012_399.dfy uses.
method Solve(n: int, transactions: seq<seq<string>>) returns (output: string, ghost steps: nat)
  ensures steps <= 4050 * (if n > 0 then n else 0) + 5
{
  steps := 2;
  var d: seq<int> := seq(2009, _ => 0);
  var ans := 0;
  var i := 0;
  while i < n
    invariant 0 <= i
    invariant i > 0 ==> i <= n
    invariant |d| == 2009
    invariant steps <= 4050 * i + 4
    decreases n - i
  {
    steps := steps + 34;
    if i < |transactions| && |transactions[i]| >= 2 {
      var kind := transactions[i][0];
      var x := ParseInt(transactions[i][1]);
      if 0 <= x < |d| {
        if kind == "win" {
          var p := 1;
          var e := 0;
          while e < x
            invariant 0 <= e <= x
            invariant steps <= 4050 * i + 38 + 2 * e
            decreases x - e
          {
            p := p * 2;
            e := e + 1;
            steps := steps + 2;
          }
          d := d[x := ans + p];
        } else {
          ans := if d[x] > ans then d[x] else ans;
        }
      }
    }
    i := i + 1;
  }
  assert i == (if n > 0 then n else 0);
  output := IntToString(ans);
  steps := steps + 1;
}
