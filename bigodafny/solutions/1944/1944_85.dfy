// 1550_A. Find The Array  (problem 1944, solution 1944_85)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// for _ in range(int(input())):
//     n=int(input())
//     if n==1: print(1);continue
//     if n==2: print(2);continue
//     if n==3: print(2);continue
//     S=1
//     c=1
//     for i in range(3,n+5,2):
//         if S==n:
//             break
//         if i+S<=n:
//             S=S+i
//             c+=1
//         else:
//             #print('enter')
//             S=n
//             c+=1
//         #print("S",S)
//     print(c)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
  decreases *
{
  var results: seq<string> := [];
  var idx := 0;
  while idx < |numbers|
    decreases |numbers| - idx
  {
    var nn := numbers[idx];
    var c: int;
    if nn == 1 {
      c := 1;
    } else if nn == 2 {
      c := 2;
    } else if nn == 3 {
      c := 2;
    } else {
      var S := 1;
      var cc := 1;
      var i := 3;
      while i < nn + 5 && S != nn
        decreases *
      {
        if i + S <= nn {
          S := S + i;
        } else {
          S := nn;
        }
        cc := cc + 1;
        i := i + 2;
      }
      c := cc;
    }
    results := results + [IntToString(c)];
    idx := idx + 1;
  }
  output := Join(results, "\n");
}
