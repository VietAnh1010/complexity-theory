// 1365_C. Rotation Matching  (problem 2188, solution 2188_359)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int,input().split()))
// b = list(map(int,input().split()))
// dif = [0]*n
// a = list(enumerate(a))
// b = list(enumerate(b))
// a.sort(key = lambda x:x[1])
// b.sort(key = lambda x:x[1])
// for i in range(n):
//     q1 = a[i][0]
//     q2 = b[i][0]
//     if q2-q1<0:
//         dif[i]=(n+(q2-q1))
//     else:
//         dif[i]=(q2-q1)
// maxi = 0
// difmax = [0]*n
// for s in dif:
//     difmax[s]+=1
//     if difmax[s]>maxi:
//         maxi = difmax[s]
// print(maxi)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  var aPairs: seq<(int,int)> := [];
  var bPairs: seq<(int,int)> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    aPairs := aPairs + [(i, a_list[i])];
    bPairs := bPairs + [(i, b_list[i])];
    i := i + 1;
  }
  var aSorted := Sort(aPairs, (x: (int,int), y: (int,int)) => x.1 < y.1);
  var bSorted := Sort(bPairs, (x: (int,int), y: (int,int)) => x.1 < y.1);
  var dif: seq<int> := [];
  i := 0;
  while i < n
    decreases n - i
  {
    var q1 := aSorted[i].0;
    var q2 := bSorted[i].0;
    var d := if q2 - q1 < 0 then n + (q2 - q1) else q2 - q1;
    dif := dif + [d];
    i := i + 1;
  }
  var difmax := seq(if n >= 0 then n else 0, _ => 0);
  var maxi := 0;
  i := 0;
  while i < |dif|
    decreases |dif| - i
  {
    var s := dif[i];
    difmax := difmax[s := difmax[s] + 1];
    if difmax[s] > maxi { maxi := difmax[s]; }
    i := i + 1;
  }
  output := IntToString(maxi);
}
