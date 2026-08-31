// 1038_D. Slime  (problem 241, solution 241_47)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// if n==1:
//     print(a[0])
// elif all(ele>0 for ele in a):
//     s=sum(a)-2*min(a) 
//     print(s)
// elif all(ele<0 for ele in a):
//     s=abs(sum(a))-2*abs(max(a))
//     print(s)
// else:
//     ans=0 
//     for ele in a:
//         ans+=abs(ele)
//     print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  if n == 1 {
    output := IntToString(a_list[0]);
  } else {
    var allPos := true;
    var allNeg := true;
    var k := 0;
    while k < n
      decreases n - k
    {
      if a_list[k] <= 0 { allPos := false; }
      if a_list[k] >= 0 { allNeg := false; }
      k := k + 1;
    }
    var ans: int;
    if allPos {
      ans := SumRange(a_list, 0, n) - 2 * MinSeq(a_list);
    } else if allNeg {
      var total := SumRange(a_list, 0, n);
      var mx := MaxSeq(a_list);
      ans := AbsInt(total) - 2 * AbsInt(mx);
    } else {
      var total := 0;
      var j := 0;
      while j < n
        decreases n - j
      {
        total := total + AbsInt(a_list[j]);
        j := j + 1;
      }
      ans := total;
    }
    output := IntToString(ans);
  }
}

function SumRange(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0 else s[lo] + SumRange(s, lo + 1, hi)
}

function AbsInt(x: int): int
{
  if x < 0 then -x else x
}


