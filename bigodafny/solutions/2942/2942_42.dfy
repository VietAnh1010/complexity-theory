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

method Solve(n: int, transactions: seq<seq<string>>) returns (output: string)
{
  var d: seq<int> := seq(2009, _ => 0);
  var ans := 0;
  var i := 0;
  while i < n
    invariant 0 <= i
    invariant |d| == 2009
    decreases n - i
  {
    if i < |transactions| && |transactions[i]| >= 2 {
      var kind := transactions[i][0];
      var x := ParseInt(transactions[i][1]);
      if 0 <= x < |d| {
        if kind == "win" {
          var p := 1;
          var e := 0;
          while e < x
            invariant 0 <= e <= x
            decreases x - e
          {
            p := p * 2;
            e := e + 1;
          }
          d := d[x := ans + p];
        } else {
          ans := if d[x] > ans then d[x] else ans;
        }
      }
    }
    i := i + 1;
  }
  output := IntToString(ans);
}
