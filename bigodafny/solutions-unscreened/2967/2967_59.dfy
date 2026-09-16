// 399_A. Pages  (problem 2967, solution 2967_59)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,p,k=map(int,input().split(" "))
// ans=""
// if p-k>1:
//     ans+='<< '
// for i in range(p-k, p+k+1):
//     if i>0 and i<=n:
//         if i==p:
//             ans+='('+str(p)+') '
//         else:
//             ans+=str(i)+' '
// if p+k<n:
//     ans+='>>'
// if ans[len(ans)-1]==" ":
//     print(ans[0:len(ans)-1])
// else:
//     print(ans)
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
  var lo := if p - k < 1 then 1 else p - k;
  var top := if p + k > n then n else p + k;
  var i := lo;
  while i <= top
    decreases top - i
  {
    if i == p {
      tokens := tokens + ["(" + IntToString(p) + ")"];
    } else {
      tokens := tokens + [IntToString(i)];
    }
    i := i + 1;
  }
  if p + k < n {
    tokens := tokens + [">>"];
  }
  output := Join(tokens, " ") + "\n";
}
