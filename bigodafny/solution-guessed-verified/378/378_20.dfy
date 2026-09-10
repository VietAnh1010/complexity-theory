// 378_20 (problem 378) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n**2)
//   proved bound    : (BIG * n + BIG + 5) + BIG * (n + 1) * n + BIG * (n + 1) * (n + 1)
//   proved class    : unclassified
//   agent verdict   : proves
//   reference label : O(n*m)
//   prediction correct against the label: False
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     Second loop does `lines := lines + [x]` (seq append, real cost
//     |lines|) inside a loop of n iterations -- sum 0..n-1 is quadratic,
//     even though the loop body otherwise looks linear.
//
//   agent notes:
//     Charged the seq-append (|lines|<=n) and Join (sum of line lengths,
//     O(n) each) flatly as BIG*(n+1) per iteration / BIG*(n+1)^2 once; BIG
//     is huge so it safely dominates the real O(1) map ops and IntToString
//     cost too. Verified 5/5, 0 errors first try.
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 378_20
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
// n=int(input())
// x=[]
// for i in range(n):
//     x.append(list(map(int,input().split())))
//  
// h={}
// a={}
// for i in range(n):
//     if(h.get(str(x[i][0]))):
//         h[str(x[i][0])]+=1
//     else:
//         h[str(x[i][0])]=1
//     
// for i in range(n):
//     home=n-1
//     if(h.get(str(x[i][1]))):
//         if(h[str(x[i][1])]>0):
//             away= n-1-h[str(x[i][1])]
//             home+=h[str(x[i][1])]
//     else:
//         away=n-1
//     print(home,away)
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

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

// Generous fixed constant: real per-op cost here is O(1) (map get/set,
// bounded-length ParseInt) except the seq append in the second loop, whose
// real cost is |lines| <= n, and Join's real cost (sum of line lengths,
// itself bounded by O(n) per line). BIG safely dominates all of these.
ghost const BIG: nat := 3000000000000000000

method Solve(n: int, pairs: seq<seq<string>>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
  // Problem statement: "next n lines" describe the n teams, so the number of
  // rows equals n.
  requires |pairs| == n
  ensures steps <= (BIG * n + BIG + 5) + BIG * (n + 1) * n + BIG * (n + 1) * (n + 1)
{
  var h: map<int, int> := map[];
  var idx := 0;
  steps := 1;
  while idx < |pairs|
    invariant 0 <= idx <= |pairs|
    invariant steps <= BIG * idx + BIG + 5
    decreases |pairs| - idx
  {
    var home0 := ParseInt(pairs[idx][0]);
    if home0 in h {
      h := h[home0 := h[home0] + 1];
    } else {
      h := h[home0 := 1];
    }
    steps := steps + BIG;
    idx := idx + 1;
  }
  var lines: seq<string> := [];
  idx := 0;
  while idx < |pairs|
    invariant 0 <= idx <= |pairs|
    invariant steps <= (BIG * |pairs| + BIG + 5) + BIG * (n + 1) * idx
    decreases |pairs| - idx
  {
    var away0 := ParseInt(pairs[idx][1]);
    var home := n - 1;
    var away := n - 1;
    if away0 in h {
      var cnt := h[away0];
      away := n - 1 - cnt;
      home := home + cnt;
    }
    // real cost of this append is |lines| (<= n); folded into the flat
    // per-iteration charge BIG * (n + 1) along with the O(1)/O(n) rest.
    lines := lines + [IntToString(home) + " " + IntToString(away)];
    steps := steps + BIG * (n + 1);
    idx := idx + 1;
  }
  // Join's real cost is the total output length, itself O(n) per line for
  // n lines -- again folded into a flat, generously large charge.
  output := Join(lines, "\n");
  steps := steps + BIG * (n + 1) * (n + 1);
}
