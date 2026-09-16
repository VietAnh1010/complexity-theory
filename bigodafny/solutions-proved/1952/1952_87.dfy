// 877_B. Nikita and string  (problem 1952, solution 1952_87)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// n=len(s)
// counta=[0]*(n+1)
// countb=[0]*(n+1)
// ans=0
// curra=0
// currb=0
// for i in range(n):
//   if s[i]=='a':
//     curra+=1
//   else:
//     currb+=1
//   counta[i+1]=curra
//   countb[i+1]=currb
// for i in range(n+1):
//   for j in range(i,n+1):
//     ans=max(ans,countb[j]-countb[i]+counta[i]+counta[n]-counta[j])
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma DistribStep(a: nat, K: nat)
  ensures (a + 1) * K == a * K + K
{ }

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 8 * |s| * |s| + 30 * |s| + 20
{
  steps := 1;
  var n := |s|;
  var counta: seq<int> := [0];
  var countb: seq<int> := [0];
  var curra := 0;
  var currb := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |counta| == i + 1
    invariant |countb| == i + 1
    invariant steps == 4 * i + 1
    decreases n - i
  {
    if s[i] == 'a' {
      curra := curra + 1;
    } else {
      currb := currb + 1;
    }
    counta := counta + [curra];
    countb := countb + [currb];
    i := i + 1;
    steps := steps + 4;
  }
  var ans := 0;
  var ii := 0;
  while ii <= n
    invariant 0 <= ii <= n + 1
    invariant |counta| == n + 1
    invariant |countb| == n + 1
    invariant steps <= 4 * n + 1 + ii * (7 * (n + 1) + 2)
    decreases n - ii
  {
    var jj := ii;
    while jj <= n
      invariant ii <= jj <= n + 1
      invariant |counta| == n + 1
      invariant |countb| == n + 1
      invariant steps <= 4 * n + 1 + ii * (7 * (n + 1) + 2) + 7 * (jj - ii)
      decreases n - jj
    {
      var v := countb[jj] - countb[ii] + counta[ii] + counta[n] - counta[jj];
      if v > ans {
        ans := v;
      }
      jj := jj + 1;
      steps := steps + 7;
    }
    DistribStep(ii, 7 * (n + 1) + 2);
    ii := ii + 1;
    steps := steps + 2;
  }
  output := IntToString(ans);
  steps := steps + 1;
  assert ii == n + 1;
  assert steps <= 4 * n + 1 + (n + 1) * (7 * (n + 1) + 2) + 1;
}
