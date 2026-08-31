// 8_B. Obsession with Robots  (problem 949, solution 949_67)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # maa chudaaye duniya
// d = [[0,1], [0, -1], [1, 0], [-1, 0], [0, 0]]
// 
// path = input()
// 
// vis = []
// cur = [0, 0]
// f = True
// for p in path:
// 	prev = cur
// 	if p == 'L': index = 0
// 	elif p == 'R' : index = 1
// 	elif p == 'U' : index = 2
// 	else: index = 3
// 	cur = [cur[0] + d[index][0], cur[1] + d[index][1]]
// 	if cur in vis:
// 		f = False
// 		print('BUG')
// 		break
// 	for dx, dy in d:
// 		vis.append([prev[0] + dx, prev[1] + dy])
// if f:
// 	print('OK')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(directions: string) returns (output: string)
{
  var cur := (0, 0);
  var vis: set<(int, int)> := {};
  var bug := false;
  var i := 0;
  while i < |directions| && !bug
    decreases |directions| - i
  {
    var prev := cur;
    var p := directions[i];
    var idx := if p == 'L' then 0 else if p == 'R' then 1 else if p == 'U' then 2 else 3;
    var dx := if idx == 2 then 1 else if idx == 3 then -1 else 0;
    var dy := if idx == 0 then 1 else if idx == 1 then -1 else 0;
    cur := (cur.0 + dx, cur.1 + dy);
    if cur in vis {
      bug := true;
    } else {
      vis := vis + {(prev.0, prev.1 + 1), (prev.0, prev.1 - 1), (prev.0 + 1, prev.1), (prev.0 - 1, prev.1), (prev.0, prev.1)};
    }
    i := i + 1;
  }
  output := (if bug then "BUG" else "OK") + "\n";
}
