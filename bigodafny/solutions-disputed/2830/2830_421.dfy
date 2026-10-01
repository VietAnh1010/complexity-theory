// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve has a fill loop and one `while i < n` loop (in either the even
//     or the odd branch) that writes buf[pos] in O(1), so it is O(n). The
//     Python does the same single loop over range(n) with ''.join at the
//     end, so it is O(n) and the O(n**2) label is wrong.
//
//   how this label could be wrong, and what to check:
//     The label assumes some nested quadratic work. Check the three loops
//     in Solve: the buffer fill, and the two branches that each run a
//     single `while i < n` with an O(1) body; none nests, so it is linear.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 40, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 3,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 746_B. Decoding  (problem 2830, solution 2830_421)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def solution(n,s):
// 	ans = [" "]*n
// 
// 	if n%2==0:
// 		p = int(n/2) - 1
// 		for i in range(n):
// 			if i%2==0:
// 				ans[p - int(i/2) ] = s[i]
// 			else:
// 				ans[p + int((i+1)/2) ] = s[i]
// 	else:
// 		p = int(n/2)
// 		for i in range(n):
// 			if i%2==0:
// 				ans[p + int(i/2) ] = s[i]
// 			else:
// 				ans[p - int((i+1)/2) ] = s[i]	
// 	return ''.join(ans)
// 
// n = int(input())
// s = input()
// print(solution(n,s))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  var sz := if n > 0 then n else 0;
  var buf := new char[sz];
  var k := 0;
  while k < n
    invariant 0 <= k <= sz
  {
    buf[k] := ' ';
    k := k + 1;
  }
  if n % 2 == 0 {
    var p := n / 2 - 1;
    var i := 0;
    while i < n
      invariant 0 <= i <= sz
    {
      var pos := if i % 2 == 0 then p - i / 2 else p + (i + 1) / 2;
      if 0 <= pos < n && i < |s| {
        buf[pos] := s[i];
      }
      i := i + 1;
    }
  } else {
    var p := n / 2;
    var i := 0;
    while i < n
      invariant 0 <= i <= sz
    {
      var pos := if i % 2 == 0 then p + i / 2 else p - (i + 1) / 2;
      if 0 <= pos < n && i < |s| {
        buf[pos] := s[i];
      }
      i := i + 1;
    }
  }
  output := buf[0..sz];
}
