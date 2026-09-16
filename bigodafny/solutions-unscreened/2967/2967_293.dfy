// 399_A. Pages  (problem 2967, solution 2967_293)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,p,k = map(int,input().split())
// if((p-k)>1):
//     print("<<",end=" ")
// for i in range(p-k,p+k+1):
//     if(i<1) or (i>n):
//         continue
//     elif(i==p):
//         print("(" + str(i) + ")",end=" ")
//     else:
//         print(str(i),end=" ")
// if((p+k)<n):
//     print(">>")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: string, v_1: string, v_2: string) returns (output: string)
{
  var n := ParseInt(v_0);
  var p := ParseInt(v_1);
  var k := ParseInt(v_2);
  var tokens: seq<string> := [];
  if p - k > 1 {
    tokens := tokens + ["<<"];
  }
  var i := p - k;
  var hi := p + k;
  while i <= hi
    decreases hi - i
  {
    if i >= 1 && i <= n {
      if i == p {
        tokens := tokens + ["(" + IntToString(i) + ")"];
      } else {
        tokens := tokens + [IntToString(i)];
      }
    }
    i := i + 1;
  }
  if p + k < n {
    tokens := tokens + [">>"];
  }
  output := Join(tokens, " ") + "\n";
}
