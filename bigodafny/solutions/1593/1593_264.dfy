// 977_B. Two-gram  (problem 1593, solution 1593_264)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
// l = []
// from collections import Counter
// for i in range(0,len(s)-1):
//     l.append(s[i:i+2])
// l = Counter(l)
// l = dict(l)
// max = 0
// for word in l:
//     if l[word] > max:
//         max = l[word]
//         string = word
// 
// print(string)
// 
//         
// 
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var n := |s|;
  var bestCount := 0;
  var bestStr := "";
  var i := 0;
  while i < n - 1
    decreases n - 1 - i
  {
    var cur := s[i..i+2];
    var cnt := 0;
    var j := 0;
    while j < n - 1
      decreases n - 1 - j
    {
      if s[j..j+2] == cur {
        cnt := cnt + 1;
      }
      j := j + 1;
    }
    if cnt > bestCount {
      bestCount := cnt;
      bestStr := cur;
    }
    i := i + 1;
  }
  output := bestStr;
}
