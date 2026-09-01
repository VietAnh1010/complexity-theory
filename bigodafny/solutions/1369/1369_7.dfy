// p02721 AtCoder Beginner Contest 161 - Yutori  (problem 1369, solution 1369_7)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k,c=map(int,input().split())
// s=list(input())
// i=0
// l=[0]*k
// r=[0]*k
// j=0
// while i<n and l[-1]==0:
//   if s[i]=='o':
//     l[j]=i+1
//     i+=c+1
//     j+=1
//   else:
//     i+=1
// i=0
// j=k-1
// while i<n and r[0]==0:
//   if s[-i-1]=='o':
//     r[j]=n-i
//     i+=c+1
//     j-=1
//   else:
//     i+=1
// for i in range(k):
//   if r[i]==l[i]:
//     print(r[i])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a: int, b: int, s: string) returns (output: string)
{
  var N := n;
  var K := a;
  var C := b;
  var l := seq(K, _ => 0);
  var r := seq(K, _ => 0);
  var i := 0;
  var j := 0;
  while i < N && l[K - 1] == 0
    decreases N - i
  {
    if s[i] == 'o' {
      l := l[j := i + 1];
      i := i + C + 1;
      j := j + 1;
    } else {
      i := i + 1;
    }
  }
  i := 0;
  j := K - 1;
  while i < N && r[0] == 0
    decreases N - i
  {
    if s[N - i - 1] == 'o' {
      r := r[j := N - i];
      i := i + C + 1;
      j := j - 1;
    } else {
      i := i + 1;
    }
  }
  var parts: seq<string> := [];
  var k := 0;
  while k < K
    decreases K - k
  {
    if r[k] == l[k] {
      parts := parts + [IntToString(r[k])];
    }
    k := k + 1;
  }
  output := Join(parts, "\n");
}
