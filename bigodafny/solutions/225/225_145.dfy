// 390_A. Inna and Alarm Clock  (problem 225, solution 225_145)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// d1={}
// d2={}
// n=int(input())
// l=[]
// for i in range(n):
//     x=list(map(int,input().split()))
//     l.append(x)
// for i in range(n):
//     if(l[i][0] not in d1):
//         d1[l[i][0]]=1
// sum1=sum(d1.values())
// for i in range(n):
//     if(l[i][1] not in d2):
//         d2[l[i][1]]=1
// sum2=sum(d2.values())
// print(sum1) if(sum1<=sum2) else print(sum2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<seq<int>>) returns (output: string)
{
  var xs: set<int> := {};
  var ys: set<int> := {};
  var i := 0;
  while i < n
    decreases n - i
  {
    xs := xs + {coordinates[i][0]};
    ys := ys + {coordinates[i][1]};
    i := i + 1;
  }
  var sx := |xs|;
  var sy := |ys|;
  output := IntToString(if sx <= sy then sx else sy);
}
