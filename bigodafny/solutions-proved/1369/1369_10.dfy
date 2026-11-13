// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny's two `while` loops advance `pos` monotonically across s,
//     at most N steps each, and the final loop runs K <= N times, so the
//     cost is O(N); the Python's sweeps are identical and nothing nests.
//
//   how this label could be wrong, and what to check:
//     The label is quadratic, but the code is two greedy sweeps over S,
//     one forward and one backward, each moving `n` monotonically, then
//     one loop over K <= N. Check that neither sweep restarts; then the
//     class is O(N).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 70, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 3, "recursive_helpers": 2,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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

method Solve(n: int, a: int, b: int, s: string) returns (output: string, ghost steps: nat)
  requires n == |s| && a >= 1 && b >= 0
  requires GreedyL(s, b, 0) >= a
  requires GreedyR(s, b, n - 1) >= a
  ensures steps <= 25 * n + 20 + 2 * |output|
{
  steps := 6;
  var N := n;
  var K := a;
  var C := b;
  var L := seq(K, _ => 0);
  var R := seq(K, _ => 0);
  var pos := 0;
  var lc := 0;
  ghost var it := 0;
  while lc != K
    invariant 0 <= lc <= K && |L| == K && pos >= 0
    invariant lc <= it <= pos && it <= |s|
    invariant steps <= 6 + 8 * it
    invariant lc + GreedyL(s, C, pos) >= K
    decreases K - lc, |s| - pos
  {
    steps := steps + 8;
    it := it + 1;
    if s[pos] == 'o' {
      L := L[lc := pos + 1];
      pos := pos + C + 1;
      lc := lc + 1;
    } else {
      pos := pos + 1;
    }
  }
  steps := steps + 2 * K + 4;
  pos := N - 1;
  var rc := 0;
  ghost var it2 := 0;
  ghost var base2 := steps;
  while rc != K
    invariant 0 <= rc <= K && |R| == K && pos < |s|
    invariant rc <= it2 <= |s| && it2 + pos + 1 <= |s|
    invariant steps <= base2 + 8 * it2
    invariant rc + GreedyR(s, C, pos) >= K
    decreases K - rc, pos + 1
  {
    steps := steps + 8;
    it2 := it2 + 1;
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
  ghost var base3 := steps;
  while i < K
    invariant 0 <= i <= K
    invariant |parts| <= i
    invariant steps <= base3 + 6 * i + SumLen(parts)
    decreases K - i
  {
    steps := steps + 6;
    if R[i] == L[i] {
      ghost var x := IntToString(R[i]);
      IntToStringDigits(R[i]);
      SumLenSnoc(parts, x);
      steps := steps + |x|;
      parts := parts + [IntToString(R[i])];
    }
    i := i + 1;
  }
  output := Join(parts, "\n");
  steps := steps + SumLen(parts) + |parts|;
  if |parts| >= 1 { JoinLen(parts, "\n"); }
}
