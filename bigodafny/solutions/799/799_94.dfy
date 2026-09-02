// 43_B. Letter  (problem 799, solution 799_94)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// a = list(input())
// 
// 
// b =(input())
// h=0
// 
// for k in b:
//     if k!=' ':
//         if k in a:
//             a.remove(k)
//         else:
//             print('NO')
//             h+=1
//             break
// 
// 
// if h==0:
//     print('YES')
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
    if c in counts {
      counts := counts[c := counts[c] + 1];
    } else {
      counts := counts[c := 1];
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
      if c in counts && counts[c] > 0 {
        counts := counts[c := counts[c] - 1];
      } else {
        ans := "NO";
        broke := true;
      }
    }
    i := i + 1;
  }
  output := ans + "\n";
}
