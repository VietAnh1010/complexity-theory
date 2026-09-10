// 1338_61 (problem 1338) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n*m)
//   proved bound    : |queries| * (4 * n * n + |queries| + 6) + 6
//   proved class    : unclassified
//   agent verdict   : refutes
//   reference label : O(n*m)
//   prediction correct against the label: True
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     outer loop over m queries, inner loop removes <=n elements via
//     FindMinIndex+RemoveAt, read at a glance as O(n) work per query
//
//   agent notes:
//     RemoveAt does s[..idx]+s[idx+1..] (concat cost |s|), and ReverseSeq
//     recurses with a trailing append -- both real-cost O(current size), not
//     O(1). Inner loop removes up to n elements at cost up to n each:
//     Theta(n^2) per query. parts:=parts+[...] each query also costs up to
//     |parts|<=m, adding a Theta(m^2) term. True bound is O(m*n^2+m^2), not
//     a single vocabulary class.
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 1338_61
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
// import copy
// a=[]
// ai=[]
// otv=''
// n=int(input())
// a=list(map(int,input().split()))
// m=int(input())
// for i in range(1,m+1):
//     #print(ai)
//     #print(a,'kkkk')
//     ai=copy.deepcopy(a)
//     ai.reverse()
//     #print(ai)
//     k,pos=map(int,input().split())
//     for j in range(1,n-k+1):
//         #print(min(ai))
//         ai.remove(min(ai))
//     ai.reverse()
//     otv=otv+'\n'+str(ai[pos-1])
// print(otv)
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ReverseSeq(s: seq<int>): seq<int>
  ensures |ReverseSeq(s)| == |s|
  decreases |s|
{
  if |s| == 0 then [] else ReverseSeq(s[1..]) + [s[0]]
}

function FindMinIndexFrom(s: seq<int>, i: int, best: int): int
  requires 0 <= best < |s|
  requires 0 <= i <= |s|
  ensures 0 <= FindMinIndexFrom(s, i, best) < |s|
  decreases |s| - i
{
  if i == |s| then best
  else if s[i] < s[best] then FindMinIndexFrom(s, i + 1, i)
  else FindMinIndexFrom(s, i + 1, best)
}

function FindMinIndex(s: seq<int>): int
  requires |s| > 0
  ensures 0 <= FindMinIndex(s) < |s|
{
  FindMinIndexFrom(s, 1, 0)
}

function RemoveAt(s: seq<int>, idx: int): seq<int>
  requires 0 <= idx < |s|
  ensures |RemoveAt(s, idx)| == |s| - 1
{
  s[..idx] + s[idx + 1..]
}

// isolated per GUIDE.md: nonlinear facts kept out of the main proof
lemma MulMonoLeft(x: nat, y: nat, c: nat)
  requires x <= y
  ensures x * c <= y * c
{}

// running total of k charges of C, defined additively so the loop body
// only ever needs the recursive unfolding, not a multiplication fact
ghost function TotalBound(k: nat, C: nat): nat
  decreases k
{
  if k == 0 then 0 else TotalBound(k - 1, C) + C
}

lemma TotalBoundIsMul(k: nat, C: nat)
  ensures TotalBound(k, C) == k * C
  decreases k
{
  if k > 0 { TotalBoundIsMul(k - 1, C); }
}

method Solve(n: int, a_list: seq<int>, q: int, queries: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires forall qq :: 0 <= qq < |queries| ==> 1 <= queries[qq].0 <= n
  ensures steps <= |queries| * (4 * n * n + |queries| + 6) + 6
{
  steps := 1;
  ghost var m := |queries|;
  ghost var QC: nat := 4 * n * n + m + 6;
  var parts: seq<string> := [];
  var qi := 0;
  while qi < |queries|
    invariant 0 <= qi <= |queries|
    invariant steps <= TotalBound(qi, QC) + 5
    invariant |parts| <= qi
    decreases |queries| - qi
  {
    ghost var stepsBefore := steps;
    var kk := queries[qi].0;
    var pos := queries[qi].1;
    var ai := ReverseSeq(a_list);
    steps := steps + n * n + 1;
    var removeCount := if n - kk > 0 then n - kk else 0;
    var jcount := 0;
    while jcount < removeCount
      invariant 0 <= jcount <= removeCount
      invariant |ai| == n - jcount
      invariant removeCount <= n
      invariant steps <= stepsBefore + (n * n + 1) + jcount * (2 * n) + 1
      decreases removeCount - jcount
    {
      var mi := FindMinIndex(ai);
      ai := RemoveAt(ai, mi);
      steps := steps + 2 * n;
      jcount := jcount + 1;
    }
    MulMonoLeft(removeCount, n, 2 * n);
    assert removeCount * (2 * n) <= 2 * n * n;
    assert steps <= stepsBefore + 3 * n * n + 2;
    ai := ReverseSeq(ai);
    steps := steps + n * n + 1;
    assert steps <= stepsBefore + 4 * n * n + 3;
    // parts grows by one element of bounded length; charge the append its
    // real cost |parts| <= m (loose upper bound, honest per the append rule)
    if 0 <= pos - 1 < |ai| {
      parts := parts + ["\n" + IntToString(ai[pos - 1])];
      steps := steps + m + 1;
    } else {
      steps := steps + 1;
    }
    assert steps <= stepsBefore + 4 * n * n + m + 4;
    assert stepsBefore <= TotalBound(qi, QC) + 5;
    assert steps <= TotalBound(qi, QC) + QC + 5;
    qi := qi + 1;
    assert TotalBound(qi, QC) == TotalBound(qi - 1, QC) + QC;
  }
  TotalBoundIsMul(|queries|, QC);
  assert m == |queries|;
  assert QC == 4 * n * n + |queries| + 6;
  assert steps <= |queries| * QC + 5;
  output := Join(parts, "") + "\n";
  steps := steps + 1;
}
