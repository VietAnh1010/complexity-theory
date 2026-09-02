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

method Solve(n: int, a: int, b: int, s: string) returns (output: string)
{
  var N := n;
  var K := a;
  var C := b;
  var left: seq<int> := [];
  var right: seq<int> := [];
  var i := 0;
  while |left| <= K - 1
    decreases K - |left|
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
    decreases K - |right|
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
