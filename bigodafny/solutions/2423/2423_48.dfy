// 441_B. Valera and Fruits  (problem 2423, solution 2423_48)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def a():	
// 	n, v = list(map(int, input().split(" ")))
// 	d = []
// 	for i in range(n):
// 		d.append(list(map(int, input().split(" "))))
// 	d.sort()
// 
// 	cur = 0
// 	nex = 0
// 	k = 0
// 	r = 0
// 	for i in range(d[-1][0] + 2):
// 		nex = 0
// 		p = v
// 		if k != n:
// 			while(d[k][0] < i):
// 				k += 1
// 				if k == n:
// 					break
// 		if k != n:
// 			while(d[k][0] == i):
// 				nex += d[k][1]
// 				k += 1
// 				if k == n:
// 					break
// 		r += min(p, cur)
// 		p -= min(p, cur)
// 		r += min(p, nex)
// 		cur = nex - min(p, nex)
// 	return r
// 
// print(a())
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, pairs: seq<(int, int)>) returns (output: string)
{
  var d := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  var cur := 0;
  var nex := 0;
  var idx := 0;
  var r := 0;
  var limit := d[|d| - 1].0 + 2;
  var i := 0;
  while i < limit
    decreases limit - i
  {
    nex := 0;
    var p := k;
    while idx < n && d[idx].0 < i
      decreases n - idx
    {
      idx := idx + 1;
    }
    while idx < n && d[idx].0 == i
      decreases n - idx
    {
      nex := nex + d[idx].1;
      idx := idx + 1;
    }
    var m1 := if p < cur then p else cur;
    r := r + m1;
    p := p - m1;
    var m2 := if p < nex then p else nex;
    r := r + m2;
    cur := nex - m2;
    i := i + 1;
  }
  output := IntToString(r);
}
