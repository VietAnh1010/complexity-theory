// 1005_E1. Median on Segments (Permutations Edition)  (problem 1332, solution 1332_16)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// class BIT():
//     def __init__(self,n):
//         self.BIT=[0]*(n+1)
//         self.num=n
// 
//     def query(self,idx):
//         res_sum = 0
//         while idx > 0:
//             res_sum += self.BIT[idx]
//             idx -= idx&(-idx)
//         return res_sum
// 
//     #Ai += x O(logN)
//     def update(self,idx,x):
//         while idx <= self.num:
//             self.BIT[idx] += x
//             idx += idx&(-idx)
//         return
// 
// n,m = map(int,input().split())
// a = list(map(int,input().split()))
// 
// def solve(x):
//     tmp = [0 for i in range(n)]
//     for i in range(n):
//         if a[i]>x:
//             tmp[i] = -1
//         else:
//             tmp[i] = 1
//         tmp[i] += tmp[i-1]
// 
//     tmp = [0] + tmp
//     val = list(set([tmp[j] for j in range(n+1)]))
//     val.sort()
//     comp = {i:e+1 for e,i in enumerate(val)}
// 
//     bit = BIT(n+1)
//     res = 0
//     for i in range(n+1):
//         res += bit.query(comp[tmp[i]])
//         bit.update(comp[tmp[i]],1)
//     return res
// 
// print(solve(m) - solve(m-1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Lowbit(x: int): int
  requires x > 0
  decreases x
{
  if x % 2 != 0 then 1 else 2 * Lowbit(x / 2)
}

function DedupSorted(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else if |s| == 1 then [s[0]]
  else if s[0] == s[1] then DedupSorted(s[1..])
  else [s[0]] + DedupSorted(s[1..])
}

method SolveX(n: int, a: seq<int>, x: int) returns (res: int)
  requires n == |a|
{
  var tmp2: seq<int> := [0];
  var i := 0;
  var prev := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |tmp2| == i + 1
    decreases n - i
  {
    var cur := if a[i] > x then prev - 1 else prev + 1;
    tmp2 := tmp2 + [cur];
    prev := cur;
    i := i + 1;
  }
  var vals := DedupSorted(SortInts(tmp2));
  var comp: map<int, int> := map[];
  var j := 0;
  while j < |vals|
    invariant 0 <= j <= |vals|
    decreases |vals| - j
  {
    comp := comp[vals[j] := j + 1];
    j := j + 1;
  }
  var bitArr: seq<int> := seq(n + 2, _ => 0);
  res := 0;
  var t := 0;
  while t < |tmp2|
    invariant 0 <= t <= |tmp2|
    decreases |tmp2| - t
  {
    var c := comp[tmp2[t]];
    var qidx := c;
    var sm := 0;
    while qidx > 0
      decreases qidx
    {
      sm := sm + bitArr[qidx];
      qidx := qidx - Lowbit(qidx);
    }
    res := res + sm;
    var uidx := c;
    while uidx <= n + 1
      decreases n + 1 - uidx
    {
      bitArr := bitArr[uidx := bitArr[uidx] + 1];
      uidx := uidx + Lowbit(uidx);
    }
    t := t + 1;
  }
}

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
{
  var r1 := SolveX(n, a_list, k);
  var r2 := SolveX(n, a_list, k - 1);
  output := IntToString(r1 - r2) + "\n";
}
