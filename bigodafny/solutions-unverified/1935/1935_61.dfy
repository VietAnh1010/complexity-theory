// 1023_C. Bracket Subsequence  (problem 1935, solution 1935_61)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// R = lambda:list(map(int,input().split()))
// n,t = R()
// s = input()
// 
// st = []
// req = n-t
// flag = 0
// for x in s:
//     if(x==")" and flag==0 and req>0):
//         req-=2
//         st.pop()
//         if(req==0):
//             flag = 1
//     else:
//         st.append(x)
// print("".join(st))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
  // |st| == i - 2*pops, and a pop only ever happens on a ')'. Fewer than half
  // of any prefix ending at a ')' are ')', so 2*pops <= i-1 and |st| >= 1.
  requires forall t :: 0 <= t < |s| && s[t] == ')' ==> 2 * Closes(s, t) < t
{
  var st: seq<char> := [];
  var req := n - m;
  var flag := 0;
  var i := 0;
  ghost var pops := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= pops
    invariant |st| == i - 2 * pops
    invariant pops <= Closes(s, i)
    decreases |s| - i
  {
    var x := s[i];
    if x == ')' && flag == 0 && req > 0 {
      assert 2 * Closes(s, i) < i;
      assert |st| >= 1;
      req := req - 2;
      st := st[..|st|-1];
      pops := pops + 1;
      if req == 0 { flag := 1; }
    } else {
      st := st + [x];
    }
    i := i + 1;
  }
  output := st + "\n";
}
