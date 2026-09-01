// 219_A. k-String  (problem 1582, solution 1582_315)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import defaultdict
// d=defaultdict(lambda:0)
// k=int(input())
// s=input()
// for i in s:
//     d[i]+=1
//     
// 
// f=1
// restring=""
// for i in range(97,123):
//     if d[chr(i)]:
//         if d[chr(i)]%k==0:
//             restring+=(chr(i)*(d[chr(i)]//k))
//             
//         else:
//             f=0
//             break
//         
// 
// print(restring*k if f else -1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: string) returns (output: string)
{
  var counts: seq<int> := seq(26, i => 0);
  var idx := 0;
  while idx < |v_1|
    decreases |v_1| - idx
  {
    var c := v_1[idx];
    var pos := (c as int) - ('a' as int);
    counts := counts[pos := counts[pos] + 1];
    idx := idx + 1;
  }
  var ok := true;
  var restring: string := "";
  var ci := 0;
  while ci < 26
    decreases 26 - ci
  {
    if ok && counts[ci] > 0 {
      if counts[ci] % v_0 != 0 {
        ok := false;
      } else {
        restring := restring + Repeat([(('a' as int + ci) as char)], counts[ci] / v_0);
      }
    }
    ci := ci + 1;
  }
  if ok {
    output := Repeat(restring, v_0);
  } else {
    output := "-1";
  }
}
