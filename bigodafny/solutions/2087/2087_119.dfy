// 1547_B. Alphabetical Strings  (problem 2087, solution 2087_119)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = "abcdefghijklmnopqrstuvwxyz"
// def alpha (r,n):
//     if len(r)==1 and r[0]==n:
//         print("YES")
//         return 0
//     elif r[0]==n:
//         alpha(r[1:],a[(a.find(n))-1])
//     elif r[-1]==n:
//          alpha(r[:-1],a[(a.find(n))-1])
//     else:
//         print("NO")
// k = int(input())
// for i in range(k):
//     r = str(input())
//     alpha(r,a[len(r)-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(strings: seq<string>) returns (output: string)
{
  var results: seq<string> := [];
  var si := 0;
  while si < |strings|
    decreases |strings| - si
  {
    var r := strings[si];
    var idxLetter := |r| - 1;
    var res := "";
    var done := false;
    while !done
      decreases |r|
    {
      var n := (('a' as int) + idxLetter) as char;
      if |r| == 1 {
        if r[0] == n {
          res := "YES";
        } else {
          res := "NO";
        }
        done := true;
      } else if r[0] == n {
        r := r[1..];
        idxLetter := idxLetter - 1;
      } else if r[|r| - 1] == n {
        r := r[..|r| - 1];
        idxLetter := idxLetter - 1;
      } else {
        res := "NO";
        done := true;
      }
    }
    results := results + [res];
    si := si + 1;
  }
  output := Join(results, "\n");
}
