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
  output := ""; // TODO: translate the Python above
}
