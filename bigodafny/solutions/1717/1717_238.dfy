// 300_A. Array  (problem 1717, solution 1717_238)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #A. Array
// n = int(input())
// a,b,c =[],[],[]
// l = list(map(int,input().split()))
// for i in l:
//     if i<0:
//         a.append(i)
//     elif i>0:
//         b.append(i)
//     else:
//         c.append(i)
// 
// if len(b)==0 and len(a)>2:
//     b.append(a.pop())
//     b.append(a.pop()) 
// if len(a)%2==0:
//     c.append(a.pop())    
// print(len(a),*a)
// print(len(b),*b)
// print(len(c),*c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function FormatLenAndElems(l: seq<int>): string
{
  if |l| == 0 then IntToString(0) else IntToString(|l|) + " " + JoinInts(l, " ")
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  // the problem guarantees a valid three-way split, which needs a negative
  requires exists k :: 0 <= k < |a_list| && a_list[k] < 0
{
  var a: seq<int> := [];
  var b: seq<int> := [];
  var c: seq<int> := [];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant (exists k :: 0 <= k < i && a_list[k] < 0) ==> |a| > 0
    decreases |a_list| - i
  {
    var v := a_list[i];
    if v < 0 {
      a := a + [v];
    } else if v > 0 {
      b := b + [v];
    } else {
      c := c + [v];
    }
    i := i + 1;
  }
  assert |a| > 0;
  if |b| == 0 && |a| > 2 {
    b := b + [a[|a| - 1]];
    a := a[..|a| - 1];
    b := b + [a[|a| - 1]];
    a := a[..|a| - 1];
  }
  if |a| % 2 == 0 {
    c := c + [a[|a| - 1]];
    a := a[..|a| - 1];
  }
  output := FormatLenAndElems(a) + "\n" + FormatLenAndElems(b) + "\n" + FormatLenAndElems(c);
}
