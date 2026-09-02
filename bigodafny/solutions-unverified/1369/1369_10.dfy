// p02721 AtCoder Beginner Contest 161 - Yutori  (problem 1369, solution 1369_10)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N,K,C=map(int,input().split())
// S=input()
// L=[0 for i in range(K)]
// R=[0 for i in range(K)]
// n=0
// rc=0
// lc=0
// while True:
//   if lc==K:
//     break
//   if S[n]=="o":
//     L[lc]=n+1
//     n+=C+1
//     lc+=1
//   else:
//     n+=1
// n=N-1
// while True:
//   if rc==K:
//     break
//   if S[n]=="o":
//     R[K-1-rc]=n+1
//     n-=C+1
//     rc+=1
//   else:
//     n-=1
// for i in range(K):
//   if R[i]==L[i]:
//     print(R[i])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a: int, b: int, s: string) returns (output: string)
{
  var N := n;
  var K := a;
  var C := b;
  var L := seq(K, _ => 0);
  var R := seq(K, _ => 0);
  var pos := 0;
  var lc := 0;
  while lc != K
    decreases K - lc
  {
    if s[pos] == 'o' {
      L := L[lc := pos + 1];
      pos := pos + C + 1;
      lc := lc + 1;
    } else {
      pos := pos + 1;
    }
  }
  pos := N - 1;
  var rc := 0;
  while rc != K
    decreases K - rc
  {
    if s[pos] == 'o' {
      R := R[K - 1 - rc := pos + 1];
      pos := pos - C - 1;
      rc := rc + 1;
    } else {
      pos := pos - 1;
    }
  }
  var parts: seq<string> := [];
  var i := 0;
  while i < K
    decreases K - i
  {
    if R[i] == L[i] {
      parts := parts + [IntToString(R[i])];
    }
    i := i + 1;
  }
  output := Join(parts, "\n");
}
