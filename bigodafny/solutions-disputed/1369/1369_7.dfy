// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-09
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     `l := l[j := i+1]` and `r := r[j := N-i]` are seq updates inside the
//     two while loops, each costing O(|l|)=O(K); since K can be as large
//     as N, the up to K such updates cost O(K^2), making the Dafny
//     quadratic in the worst case even though the surrounding scan is only
//     O(N).
//
//   how this label could be wrong, and what to check:
//     The label assumes Python's `l[j]=i+1` list assignment (O(1)) carries
//     over unchanged to Dafny. Check the constraint 1<=K<=N in the problem
//     statement and confirm K can reach Theta(N); then open the two while
//     loops and confirm `l := l[j := i+1]` and `r := r[j := N-i]` are seq
//     updates, not array writes.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 59, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 3, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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
  requires a >= 1
  requires b >= 0
  requires n == |s|
{
  var N := n;
  var K := a;
  var C := b;
  var l := seq(K, _ => 0);
  var r := seq(K, _ => 0);
  var i := 0;
  var j := 0;
  while i < N && l[K - 1] == 0
    invariant 0 <= i
    invariant |l| == K
    invariant l[K - 1] == 0 ==> 0 <= j <= K - 1
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
    invariant 0 <= i
    invariant |r| == K
    invariant r[0] == 0 ==> 0 <= j <= K - 1
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
    invariant 0 <= k <= K
    invariant |r| == K
    invariant |l| == K
    decreases K - k
  {
    if r[k] == l[k] {
      parts := parts + [IntToString(r[k])];
    }
    k := k + 1;
  }
  output := Join(parts, "\n");
}
