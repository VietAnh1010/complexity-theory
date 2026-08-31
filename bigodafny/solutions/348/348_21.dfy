// 24_A. Ring road  (problem 348, solution 348_21)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// source=set()
// dest=set()
// c1=0
// c2=0
// for i in range(int(input())):
//     s,d,w=map(int,input().split())
//     if s in source or d in dest:
//         c1=c1+w
//         s,d=d,s
//     else:
//         c2=c2+w
//     source.add(s)
//     dest.add(d)
// print(min(c1,c2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsInt(xs: seq<int>, x: int): bool
  decreases |xs|
{
  if |xs| == 0 then false
  else if xs[0] == x then true
  else ContainsInt(xs[1..], x)
}

method Solve(n: int, v_list: seq<seq<int>>) returns (output: string)
{
  var source: seq<int> := [];
  var dest: seq<int> := [];
  var c1 := 0;
  var c2 := 0;
  var idx := 0;
  while idx < |v_list|
    decreases |v_list| - idx
  {
    var s := v_list[idx][0];
    var d := v_list[idx][1];
    var w := v_list[idx][2];
    if ContainsInt(source, s) || ContainsInt(dest, d) {
      c1 := c1 + w;
      var tmp := s;
      s := d;
      d := tmp;
    } else {
      c2 := c2 + w;
    }
    source := source + [s];
    dest := dest + [d];
    idx := idx + 1;
  }
  output := IntToString(if c1 < c2 then c1 else c2);
}
