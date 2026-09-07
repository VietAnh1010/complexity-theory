// 68_B. Energy exchange  (problem 967, solution 967_19)
// time complexity: O(nlogn)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// l=list(map(int,input().split()))
// l.sort(reverse=True)
// s=sum(l)
// s1=0
// s2=s
// ans=0
// k=100-k
// for i in range(n-1):
// 	# ans=max(ans,(s1*k+100*s2)/((i+1)*k+100*(n-i-1)))
// 	s1+=l[i]
// 	s2-=l[i]
// 	a=(s1*k+100*s2)/((i+1)*k+100*(n-i-1))
// 	if a<=l[i] and a>=l[i+1]:
// 		ans=max(ans,a)
// 	# print (s1,s2,ans,i,s1*k+100*s2,(i+1)*k)
// if len(set(l))==1:
// 	print (l[0])
// else:
// 	print (ans)
// --------------------------------------------------------------------

// ===================================================================
// NOT TRANSLATED — and not intended to be.
//
// Blocker: print(ans) where ans is a Python float from `/` division
//
// Reproducing this byte-for-byte needs two things Dafny cannot give:
//   1. bit-exact IEEE-754 double arithmetic. Dafny's `real` is an exact
//      rational, so it does not round where a float rounds, and the two
//      diverge before any printing happens.
//   2. CPython's shortest-round-trip float repr (Grisu/Dragon4). `print(x)`
//      on a float emits the shortest decimal string that parses back to the
//      same double -- not a fixed number of digits.
//
// Detail: ans is produced by float division and printed bare.
//
// This is decidable and tractable when the Python uses a FORMAT SPEC:
// solutions/2496/2496_30.dfy computes in exact rationals and hand-writes
// FormatG9 to replicate '{:.9}'.format(x), and agrees on all 42 comparable
// tests. It is the bare `print(float)` that has no finite specification.
//
// Both gates are therefore inapplicable, not merely failing:
// validate.py and difftest.py both compare stdout as text.
// ===================================================================

