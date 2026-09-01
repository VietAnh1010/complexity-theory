// 43_B. Letter  (problem 799, solution 799_281)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a={}
// for c in input():
//     if c==" ":
//         continue
//     if c in a:
//         a[c]+=1
//     else:
//         a[c]=1
// ans="YES"
// for c in input():
//     if c==" ":
//         continue
//     if c in a:
//         if a[c]==0:
//             ans="NO"
//             break
//         else:
//             a[c]-=1
//     else:
//         ans="NO"
//         break
// print(ans)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(first_sentence: string, second_sentence: string) returns (output: string)
{
  var counts: map<char, int> := map[];
  var i := 0;
  while i < |first_sentence|
    decreases |first_sentence| - i
  {
    var c := first_sentence[i];
    if c != ' ' {
      if c in counts {
        counts := counts[c := counts[c] + 1];
      } else {
        counts := counts[c := 1];
      }
    }
    i := i + 1;
  }
  var ans := "YES";
  var broke := false;
  i := 0;
  while i < |second_sentence| && !broke
    decreases |second_sentence| - i
  {
    var c := second_sentence[i];
    if c != ' ' {
      if c in counts {
        if counts[c] == 0 {
          ans := "NO";
          broke := true;
        } else {
          counts := counts[c := counts[c] - 1];
        }
      } else {
        ans := "NO";
        broke := true;
      }
    }
    i := i + 1;
  }
  output := ans + "\n";
}
