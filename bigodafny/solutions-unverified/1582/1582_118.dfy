// 219_A. k-String  (problem 1582, solution 1582_118)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def solve():
//     n=int(input())
//     s=sorted(input(), key=(lambda x: ord(x)))
//     ind=[[s[0],1]]
//     if len(s) % n!=0:
//         print(-1)
//         return
//     for i in range(1,len(s)):
//         if s[i]!=ind[len(ind)-1][0]:
//             ind.append([s[i],1])
//         else: ind[len(ind)-1][1]+=1
//     ans=[]
//     for ii in ind:
//         if ii[1] % n!=0:
//             print(-1)
//             return
//         ans.extend([ii[0] for i in range(ii[1]//n)])
//     print("".join(ans * n))
// solve()
// 
// 
//           
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: string) returns (output: string)
{
  var sorted := Sort(v_1, (a: char, b: char) => a < b);
  var len := |sorted|;
  if len % v_0 != 0 {
    output := "-1";
  } else {
    var groups: seq<(char,int)> := [];
    var i := 0;
    while i < len
      decreases len - i
    {
      var c := sorted[i];
      if |groups| > 0 && groups[|groups|-1].0 == c {
        var last := groups[|groups|-1];
        groups := groups[..|groups|-1] + [(c, last.1 + 1)];
      } else {
        groups := groups + [(c, 1)];
      }
      i := i + 1;
    }
    var ok := true;
    var ans: string := "";
    var j := 0;
    while j < |groups|
      decreases |groups| - j
    {
      var pr := groups[j];
      if ok {
        if pr.1 % v_0 != 0 {
          ok := false;
        } else {
          ans := ans + Repeat([pr.0], pr.1 / v_0);
        }
      }
      j := j + 1;
    }
    if !ok {
      output := "-1";
    } else {
      output := Repeat(ans, v_0);
    }
  }
}
