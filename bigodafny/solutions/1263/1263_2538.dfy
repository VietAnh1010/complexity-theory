// 1352_A. Sum of Round Numbers  (problem 1263, solution 1263_2538)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// for _ in range(t):
//     n = input()
//     k = len(n.replace('0', ''))
//     print(k)
//     ln = len(n)
//     lst = [n[i]+'0'*(ln-i-1) for i in range(ln) if n[i] != '0']
//     print(*lst)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
{

  var results: seq<string> := [];
  var t := 0;
  while t < n
    decreases n - t
  {
    var v := a_list[t];
    var s := IntToString(v);
    var ln := |s|;
    var lst: seq<string> := [];
    var i := 0;
    while i < ln
      decreases ln - i
    {
      if s[i] != '0' {
        lst := lst + [[s[i]] + Repeat("0", ln - i - 1)];
      }
      i := i + 1;
    }
    results := results + [IntToString(|lst|), Join(lst, " ")];
    t := t + 1;
  }
  output := Join(results, "\n");
}
}
