// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(nlogn)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     `Norm1628b` recurses on both halves and then does `StringLess(a, b)`
//     and a concatenation, each O(|s|), giving O(n log n); the live Python
//     function has the same structure and the other variants are inside
//     string literals.
//
//   how this label could be wrong, and what to check:
//     The label is linear, but `lexicographic_minimal_string` recurses on
//     both halves and compares and concatenates them, T(n) = 2T(n/2) +
//     O(n). Check the triple-quoted blocks: they are dead strings, so the
//     live code is this recursion, O(n log n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 24, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 0, "loops": 0,
//     "recursive_helpers": 1, "seq_append_read_in_same_loop": false,
//     "seq_args": 2, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 560_D. Equivalent Strings  (problem 1628, solution 1628_32)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// 
// 
// def isEqual(a, b):
// 	for i in range(0, len(a)):
// 		if (a[i] != b[i]):
// 			return False
// 	return True
// 
// 
// def lexicographic_minimal_string(s):
// 	if (len(s) % 2 == 1):
// 		return s
// 	half = int(len(s) /2)
// 	s1 = lexicographic_minimal_string(s[:half])
// 	s2 = lexicographic_minimal_string(s[half:])
// 	if s1 < s2:
// 		return s1 + s2
// 	return s2 + s1
// 
// a = input()
// b = input()
// a = lexicographic_minimal_string(a)
// b = lexicographic_minimal_string(b)
// if(isEqual(a,b)):
// 	print("YES")
// else:
// 	print("NO")
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 
// '''
// 
// def isEqual(AS,BS,size):
// 	for i in range(0, size):
// 		if (a[AS+i] != b[BS+i]):
// 			return False
// 	return True
// 
// def equivalent(AS,BS,size):
// 	global a
// 	global b
// 
// 	if isEqual(AS,BS,size):
// 		return True
// 
// 	half = int(size / 2)
// 	if 2*half != size:
// 		return False
// 
// 	if (equivalent(AS,BS+half,half) and equivalent(AS+half,BS,half)):
// 		return True
// 
// 	if (equivalent(AS,BS,half) and equivalent(AS+half,BS+half,half)):
// 		return True
// 
// 	return False
// 
// 
// a = input()
// b = input()
// 
// if equivalent(0,0,len(a)):
// 	print("YES")
// else:
// 	print("NO")
// 
// '''
// 
// '''
// a = input()
// b = input()
// 
// def isEqual(a, b):
// 	for i in range(0, len(a)):
// 		if (a[i] != b[i]):
// 			return False
// 	return True
// 
// def equivalent(a, b):
// 	if a == "":
// 		return True
// 
// 	if isEqual(a, b):
// 		return True
// 
// 	half = int(len(a) / 2)
// 	if 2*half != len(a):
// 		return False
// 
// 	if (equivalent(a[:half], b[:half]) and equivalent(a[half:], b[half:])):
// 		return True
// 
// 	if (equivalent(a[:half], b[half:]) and equivalent(a[half:], b[:half])):
// 		return True
// 
// 	return False
// 
// 
// if equivalent(a,b):
// 	print("YES")
// else:
// 	print("NO")
// '''
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string)
  requires |s1| > 0 && |s2| > 0
{
  var na := Norm1628b(s1);
  var nb := Norm1628b(s2);
  if na == nb {
    output := "YES";
  } else {
    output := "NO";
  }
}

function Norm1628b(s: string): string
  requires |s| > 0
  decreases |s|
{
  if |s| % 2 == 1 then s
  else
    var half := |s| / 2;
    var a := Norm1628b(s[..half]);
    var b := Norm1628b(s[half..]);
    if StringLess(a, b) then a + b else b + a
}
