// 801_A. Vicious Keyboard  (problem 2589, solution 2589_115)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = input()
// import copy
// result = s.count('vk')
// 
// for i in range(len(s)):
//     news = copy.copy(s)
//     news = list(news)
//     news[i] = 'V'
//     news = ''.join(news)
//     result = max(result, news.count('VK'))
// for i in range(len(s)):
//     news = copy.copy(s)
//     news = list(news)
//     news[i] = 'K'
//     news = ''.join(news)
//     result = max(result, news.count('VK'))
// print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(string_: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
