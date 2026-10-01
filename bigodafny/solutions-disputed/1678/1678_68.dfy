// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-09
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     GcdEx recurses on (b % a, a) with no loop, costing Euclid's depth
//     O(log min(a,b)), a value term under the Gcd rule; the Python gcdEx
//     has the identical recursion, so the O(1) label ignores a value cost
//     both programs pay.
//
//   how this label could be wrong, and what to check:
//     The label treats the body as straight-line O(1), but GcdEx recurses
//     on (b % a, a), a Euclid descent of depth O(log min(a,b)) in the
//     input values. Check that GcdEx recurses with b % a and that the
//     Python gcdEx does the same; the statement's cap of 100 does not make
//     it constant.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 45, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 0, "loops": 0,
//     "recursive_helpers": 3, "seq_append_read_in_same_loop": false,
//     "seq_args": 0, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 633_A. Ebony and Ivory  (problem 1678, solution 1678_68)
// time complexity: O(1)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil
// def gcdEx(a,b,x,y):
//     if not a:
//         return 0,1,b
//     x1,y1,g=gcdEx(b%a,a,0,0)
//     x=y1-(b//a)*x1
//     y=x1
//     return x,y,g
// a,b,c=map(int, input().split())
// x,y,g=gcdEx(a,b,0,0)
// if c%g:
//     print("No")
// else:    
//     x,y=x*c//g,y*c//g
//     k1=ceil(-x*g/b)
//     k2=(y*g)//a
//     c=abs(k2-k1+1)
//     print("Yes" if c>0 else "No")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function GcdEx(a: int, b: int): (int, int, int)
  decreases if a < 0 then -a else a
{
  if a == 0 then (0, 1, b)
  else
    var r := GcdEx(b % a, a);
    (r.1 - (b / a) * r.0, r.0, r.2)
}

// Dafny's % is Euclidean, so b % a is in [0, a) for a > 0; induct on a.
lemma GcdExPos(a: int, b: int)
  requires a >= 0 && b > 0
  ensures GcdEx(a, b).2 > 0
  decreases a
{
  if a != 0 { GcdExPos(b % a, a); }
}

function CeilDiv(p: int, q: int): int
  requires q > 0
{
  -FloorDiv(-p, q)
}

method Solve(rows: int, columns: int, value: int) returns (output: string)
  requires rows >= 1
  requires columns >= 1
{
  var a := rows;
  var b := columns;
  var c := value;
  var r := GcdEx(a, b);
  var x := r.0;
  var y := r.1;
  var g := r.2;
  GcdExPos(a, b);
  if c % g != 0 {
    output := "No";
  } else {
    var xp := FloorDiv(x * c, g);
    var yp := FloorDiv(y * c, g);
    var k1 := CeilDiv(-xp * g, b);
    var k2 := FloorDiv(yp * g, a);
    var cc := AbsInt(k2 - k1 + 1);
    output := if cc > 0 then "Yes" else "No";
  }
}
