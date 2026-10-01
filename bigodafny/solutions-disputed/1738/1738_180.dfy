// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve fills test with d = c / a entries, then for each of e = c / b
//     values scans all of test (`while k < |test|`), so the cost is the
//     product of two different value bounds, O(n*m) under the naming rule,
//     not O(n**2). The Python does the same `i*b in test` list scan inside
//     `for i in range(1, e+1)`, so the label is at fault.
//
//   how this label could be wrong, and what to check:
//     The label squares one size, but the two nested loops run to
//     different values c/a and c/b. Check that `while i <= d` fills test
//     (length d = c/a) and the later `while i <= e` scans test for each of
//     e = c/b iterations; two different value bounds multiply as n*m, not
//     n squared.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 35, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 3, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 764_A. Taymyr is calling you  (problem 1738, solution 1738_180)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// abc= input().split()
// 
// a= int(abc[0])
// b= int(abc[1])
// c= int(abc[2])
// 
// d= c//a
// e=c//b
// test=[]
// test2=[]
// count=0
// for i in range(1,d+1):
//     test.append(i*a)
// 
// for i in range(1,e+1):
//     if i*b in test:
//         count=count+1
// 
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int) returns (output: string)
  requires a >= 1
  requires b >= 1
{
  var d := c / a;
  var e := c / b;
  var test: seq<int> := [];
  var i := 1;
  while i <= d
    decreases d - i + 1
  {
    test := test + [i * a];
    i := i + 1;
  }
  var count := 0;
  i := 1;
  while i <= e
    decreases e - i + 1
  {
    var found := false;
    var k := 0;
    while k < |test|
      invariant 0 <= k <= |test|
      decreases |test| - k
    {
      if test[k] == i * b { found := true; }
      k := k + 1;
    }
    if found { count := count + 1; }
    i := i + 1;
  }
  output := IntToString(count);
}
