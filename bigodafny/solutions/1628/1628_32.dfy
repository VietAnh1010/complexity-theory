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
{
  output := ""; // TODO: translate the Python above
}
