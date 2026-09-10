// 1039_15 (problem 1039) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n**2)
//   proved bound    : 10 * (ParseInt(n_str)) * (ParseInt(n_str)) + 100 * (ParseInt(n_str)) + |a_list_str| + |n_str| + 100
//   proved class    : O(n**2)
//   agent verdict   : proves
//   reference label : O(nlogn)
//   prediction correct against the label: False
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     firstPos/lastPos are seq<int>, updated via s[x := i] inside a loop
//     over n elements; each seq update costs |s| = n+1, so n such updates
//     cost O(n^2), dominating the O(n log n) sort/binary-search parts.
//
//   agent notes:
//     Two loops do firstPos/lastPos := seq[x := i] each iteration (n iters,
//     cost n+1 each): real quadratic, matches guess. Charged SortInts and
//     the initial ParseInt/ParseIntList/SplitWs calls as flat O(n) black
//     boxes (not deriving their true recursive cost) since they're dominated
//     by the n^2 term regardless. Bounded the binary-search inner loop by
//     its trip count (<= |sortedLast|) via a linear decreases-based
//     invariant instead of CeilLog2, since log n is dominated by n^2 anyway
//     -- avoided that machinery entirely. Needed isolated multiplication
//     lemmas (i*k successor step, n*(n+10) and (n+1)*(n+10) expansion) plus
//     explicit intermediate asserts to keep Z3 from timing out on the final
//     postcondition.
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 1039_15
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
// from collections import defaultdict
// from bisect import bisect
// 
// INF = 10**9
// 
// n = int(input())
// a = list(map(int, input().split()))
// 
// first_pos = [INF] * (n+1)
// for i, x in enumerate(a):
//     if first_pos[x] == INF:
//         first_pos[x] = i
//         
// last_pos = [-1] * (n+1)
// for i, x in enumerate(a):
//     last_pos[x] = i
// last_pos.sort()
// 
// total = 0
// for i, first in enumerate(first_pos):
//     total += len(last_pos) - bisect(last_pos, first)
// print(total)
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MulSuccLemma(i: nat, k: nat)
  ensures (i + 1) * k == i * k + k
{}

lemma ExpandNTimesNPlus10(n: nat)
  ensures n * (n + 10) == n * n + 10 * n
{}

lemma ExpandNPlus1TimesNPlus10(n: nat)
  ensures (n + 1) * (n + 10) == n * n + 11 * n + 10
{}

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then -ParseIntFrom(s, 1, 0)
  else ParseIntFrom(s, 0, 0)
}

function ParseIntList(ss: seq<string>): seq<int>
  decreases |ss|
{
  if |ss| == 0 then [] else [ParseInt(ss[0])] + ParseIntList(ss[1..])
}


method Solve(n_str: string, a_list_str: string) returns (output: string, ghost steps: nat)
  requires var nums := ParseIntList(SplitWs(a_list_str));
           var n := ParseInt(n_str);
           n >= 0 && |nums| == n && forall k :: 0 <= k < |nums| ==> 1 <= nums[k] <= n
  ensures var n := ParseInt(n_str);
          steps <= 10 * n * n + 100 * n + |a_list_str| + |n_str| + 100
{
  steps := 1;
  var n := ParseInt(n_str);
  var nums := ParseIntList(SplitWs(a_list_str));
  steps := steps + |a_list_str| + |n_str| + 5;
  var INF := 1000000000;
  var firstPos := seq(n + 1, _ => INF);
  var lastPos := seq(n + 1, _ => -1);
  var i := 0;
  ghost var loop1Base := steps;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |firstPos| == n + 1
    invariant steps <= loop1Base + i * (n + 10)
    decreases |nums| - i
  {
    var x := nums[i];
    if firstPos[x] == INF {
      firstPos := firstPos[x := i];
    }
    MulSuccLemma(i, n + 10);
    steps := steps + (n + 10);
    i := i + 1;
  }
  ExpandNTimesNPlus10(n);
  assert steps <= loop1Base + n * n + 10 * n;
  assert steps <= |a_list_str| + |n_str| + 6 + n * n + 10 * n;
  i := 0;
  ghost var loop2Base := steps;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |lastPos| == n + 1
    invariant steps <= loop2Base + i * (n + 10)
    decreases |nums| - i
  {
    var x := nums[i];
    lastPos := lastPos[x := i];
    MulSuccLemma(i, n + 10);
    steps := steps + (n + 10);
    i := i + 1;
  }
  ExpandNTimesNPlus10(n);
  assert steps <= loop2Base + n * n + 10 * n;
  assert steps <= |a_list_str| + |n_str| + 6 + 2 * (n * n) + 20 * n;
  var sortedLast := SortInts(lastPos);
  steps := steps + (n + 10);
  assert steps <= |a_list_str| + |n_str| + 16 + 2 * (n * n) + 21 * n;
  var total := 0;
  i := 0;
  ghost var loop3Base := steps;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant |firstPos| == n + 1
    invariant steps <= loop3Base + i * (n + 10)
    decreases n - i
  {
    var first := firstPos[i];
    var lo := 0;
    var hi := |sortedLast|;
    ghost var innerBase := steps;
    while lo < hi
      invariant 0 <= lo <= hi <= |sortedLast|
      invariant steps <= innerBase + (|sortedLast| - (hi - lo))
      decreases hi - lo
    {
      var mid := (lo + hi) / 2;
      if sortedLast[mid] <= first {
        lo := mid + 1;
      } else {
        hi := mid;
      }
      steps := steps + 1;
    }
    total := total + (|sortedLast| - lo);
    steps := steps + 5;
    MulSuccLemma(i, n + 10);
    i := i + 1;
  }
  ExpandNPlus1TimesNPlus10(n);
  assert steps <= loop3Base + n * n + 11 * n + 10;
  assert steps <= |a_list_str| + |n_str| + 26 + 3 * (n * n) + 32 * n;
  output := IntToString(total);
  steps := steps + 5;
  assert steps <= |a_list_str| + |n_str| + 31 + 3 * (n * n) + 32 * n;
}
