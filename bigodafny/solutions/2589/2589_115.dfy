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

function CountPairFrom(s: seq<char>, a: char, b: char, i: int, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| - 1 then acc
  else if s[i] == a && s[i + 1] == b then CountPairFrom(s, a, b, i + 1, acc + 1)
  else CountPairFrom(s, a, b, i + 1, acc)
}

function CountPair(s: seq<char>, a: char, b: char): int
{
  CountPairFrom(s, a, b, 0, 0)
}

method Solve(string_: string) returns (output: string)
{
  var s := string_;
  var n := |s|;
  var result := CountPair(s, 'v', 'k');
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == n
    decreases n - i
  {
    var news := s[i := 'V'];
    var c := CountPair(news, 'V', 'K');
    if c > result { result := c; }
    i := i + 1;
  }
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == n
    decreases n - i
  {
    var news := s[i := 'K'];
    var c := CountPair(news, 'V', 'K');
    if c > result { result := c; }
    i := i + 1;
  }
  output := IntToString(result);
}
