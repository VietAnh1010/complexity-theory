// p02293 Parallel/Orthogonal  (problem 2183, solution 2183_1)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// EPS = 1e-4
// 
// #外積
// def OuterProduct(one, two):
// 	tmp = one.conjugate() * two
// 	return tmp.imag
// 
// #内積
// def InnerProduct(one, two):
// 	tmp = one.conjugate() * two
// 	return tmp.real
// 
// def solve(a, b, c, d):
// 	if abs(OuterProduct(b-a, d-c)) <= EPS:
// 		return 2
// 	elif abs(InnerProduct(b-a, d-c)) <= EPS:
// 		return 1
// 	else:
// 		return 0
// 
// n = int(input())
// for _ in range(n):
// 	pp = list(map(int, input().split()))
// 	p = [complex(pp[i], pp[i+1]) for i in range(0, 8, 2)]
// 	print(solve(p[0], p[1], p[2], p[3]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rows: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var row := rows[i];
    var px: seq<int> := [];
    var py: seq<int> := [];
    var j := 0;
    while j < 8
      decreases 8 - j
    {
      px := px + [row[j]];
      py := py + [row[j+1]];
      j := j + 2;
    }
    var one_x := px[1] - px[0];
    var one_y := py[1] - py[0];
    var two_x := px[3] - px[2];
    var two_y := py[3] - py[2];
    var cross := one_x * two_y - one_y * two_x;
    var dot := one_x * two_x + one_y * two_y;
    var res := if cross == 0 then 2 else if dot == 0 then 1 else 0;
    lines := lines + [IntToString(res)];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
