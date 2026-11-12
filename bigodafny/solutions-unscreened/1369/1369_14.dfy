// p02721 AtCoder Beginner Contest 161 - Yutori  (problem 1369, solution 1369_14)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N, K, C = map(int, input().split())
// S = input()
// left = []
// right = []
// i, j = 0, N-1
// while len(left) <= K-1:
//     if S[i] == "o":
//         left.append(i)
//         i += C+1
//     else:
//         i += 1
// while len(right) <= K-1:
//     if S[j] == "o":
//         right.append(j)
//         j -= C+1
//     else:
//         j -= 1
// right.sort()
// for n in range(K):
//     if left[n] == right[n]:
//         print(left[n] + 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function GreedyL(s: string, C: int, pos: int): nat
  requires C >= 0 && pos >= 0
  decreases |s| - pos
{
  if pos >= |s| then 0
  else if s[pos] == 'o' then 1 + GreedyL(s, C, pos + C + 1)
  else GreedyL(s, C, pos + 1)
}

function GreedyR(s: string, C: int, pos: int): nat
  requires C >= 0 && pos < |s|
  decreases pos + 1
{
  if pos < 0 then 0
  else if s[pos] == 'o' then 1 + GreedyR(s, C, pos - C - 1)
  else GreedyR(s, C, pos - 1)
}

method Solve(n: int, a: int, b: int, s: string) returns (output: string)
  requires n == |s| && a >= 1 && b >= 0
  requires GreedyL(s, b, 0) >= a
  requires GreedyR(s, b, n - 1) >= a
{
  var N := n;
  var K := a;
  var C := b;
  var left: seq<int> := [];
  var right: seq<int> := [];
  var i := 0;
  while |left| <= K - 1
    invariant |left| <= K && i >= 0
    invariant |left| + GreedyL(s, C, i) >= K
    decreases K - |left|, |s| - i
  {
    if s[i] == 'o' {
      left := left + [i];
      i := i + C + 1;
    } else {
      i := i + 1;
    }
  }
  var j := N - 1;
  while |right| <= K - 1
    invariant |right| <= K && j < |s|
    invariant |right| + GreedyR(s, C, j) >= K
    decreases K - |right|, j + 1
  {
    if s[j] == 'o' {
      right := right + [j];
      j := j - C - 1;
    } else {
      j := j - 1;
    }
  }
  right := SortInts(right);
  var parts: seq<string> := [];
  var k := 0;
  while k < K
    decreases K - k
  {
    if left[k] == right[k] {
      parts := parts + [IntToString(left[k] + 1)];
    }
    k := k + 1;
  }
  output := Join(parts, "\n");
}
