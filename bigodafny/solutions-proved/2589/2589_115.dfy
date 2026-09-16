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

// ---- proof-only cost accounting --------------------------------------
// CountPairFrom does one unit of work (comparisons + arithmetic) per
// recursive call, one call per index from i to |s|-1.
ghost function CountPairCost(s: seq<char>, i: int): nat
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| - 1 then 1 else 1 + CountPairCost(s, i + 1)
}

lemma CountPairCostBound(s: seq<char>, i: int)
  requires 0 <= i <= |s|
  ensures CountPairCost(s, i) <= |s| - i + 1
  decreases |s| - i
{
  if i >= |s| - 1 {
  } else {
    CountPairCostBound(s, i + 1);
  }
}

// Isolated multiplication: (a+1)*c == a*c + c.
lemma MulDistribAdd(a: int, c: int)
  ensures (a + 1) * c == a * c + c
{}

// Label O(n**2). Each of the 2n+1 calls to CountPair costs O(n).
method Solve(string_: string) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * |string_| * |string_| + 6 * |string_| + 5
{
  var s := string_;
  var n := |s|;
  CountPairCostBound(s, 0);
  var result := CountPair(s, 'v', 'k');
  steps := 1 + CountPairCost(s, 0);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == n
    invariant steps <= 1 + (n + 1) + i * (n + 2)
    decreases n - i
  {
    var news := s[i := 'V'];
    CountPairCostBound(news, 0);
    assert |news| == n;
    var c := CountPair(news, 'V', 'K');
    steps := steps + CountPairCost(news, 0) + 1;
    if c > result { result := c; }
    assert (i + 1) * (n + 2) == i * (n + 2) + (n + 2) by { MulDistribAdd(i, n + 2); }
    i := i + 1;
  }
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == n
    invariant steps <= 1 + (n + 1) + n * (n + 2) + i * (n + 2)
    decreases n - i
  {
    var news := s[i := 'K'];
    CountPairCostBound(news, 0);
    assert |news| == n;
    var c := CountPair(news, 'V', 'K');
    steps := steps + CountPairCost(news, 0) + 1;
    if c > result { result := c; }
    assert (i + 1) * (n + 2) == i * (n + 2) + (n + 2) by { MulDistribAdd(i, n + 2); }
    i := i + 1;
  }
  output := IntToString(result);
  steps := steps + 1;
}
