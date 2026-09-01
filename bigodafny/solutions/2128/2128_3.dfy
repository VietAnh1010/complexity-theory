// 1203_F1. Complete the Projects (easy version)  (problem 2128, solution 2128_3)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,r=map(int,input().split())
// a=[]
// b=[]
// for _ in range(n):
//     c,d=map(int,input().split())
//     if d<0:
//         b.append([c,d])
//     else:
//         a.append([c,d])
// a.sort(key = lambda x: x[0])
// b.sort(key = lambda x: x[0]+x[1],reverse=True)
// z=1
// for i in a:
//     if i[0]>r:
//         z=0
//         break
//     r+=i[1]
// for i in b:
//     if i[0]>r:
//         z=0
//         break
//     r+=i[1]
// if z==0 or r<0:
//     print('NO')
// else:
//     print('YES')
// #print(a,b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, data_list: seq<seq<int>>) returns (output: string)
{
  var r := m;
  var a: seq<(int,int)> := [];
  var b: seq<(int,int)> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var row := data_list[i];
    if row[1] < 0 {
      b := b + [(row[0], row[1])];
    } else {
      a := a + [(row[0], row[1])];
    }
    i := i + 1;
  }
  a := Sort(a, (x: (int,int), y: (int,int)) => x.0 < y.0);
  b := Sort(b, (x: (int,int), y: (int,int)) => x.0 + x.1 > y.0 + y.1);
  var z := 1;
  var stop := false;
  i := 0;
  while i < |a| && !stop
    decreases |a| - i
  {
    if a[i].0 > r {
      z := 0;
      stop := true;
    } else {
      r := r + a[i].1;
      i := i + 1;
    }
  }
  stop := false;
  i := 0;
  while i < |b| && !stop
    decreases |b| - i
  {
    if b[i].0 > r {
      z := 0;
      stop := true;
    } else {
      r := r + b[i].1;
      i := i + 1;
    }
  }
  if z == 0 || r < 0 {
    output := "NO";
  } else {
    output := "YES";
  }
}
