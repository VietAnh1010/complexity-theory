// p03776 AtCoder Beginner Contest 057 - Maximum Average Sets  (problem 3079, solution 3079_181)
// time complexity: O(n**2)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import collections
// from math import factorial
// def comb(n,r):
//     return factorial(n)//factorial(n-r)//factorial(r)
// n,a,b=map(int,input().split())
// v=list(map(int,input().split()))
// v.sort(reverse=True)
// c=collections.Counter(v)
// k=min(v[:a])
// if c[max(v)]<a:
//     ans=comb(c[k],v[:a].count(k))
// else:
//     ans=0
//     for i in range(a,min(b,c[k])+1):
//         ans+=comb(c[k],i)
// print(sum(v[:a])/a)
// print(ans)
// --------------------------------------------------------------------

// ===================================================================
// NOT TRANSLATED — and not intended to be.
//
// Blocker: print(sum(v[:a])/a) — float division printed bare
//
// Reproducing this byte-for-byte needs two things Dafny cannot give:
//   1. bit-exact IEEE-754 double arithmetic. Dafny's `real` is an exact
//      rational, so it does not round where a float rounds, and the two
//      diverge before any printing happens.
//   2. CPython's shortest-round-trip float repr (Grisu/Dragon4). `print(x)`
//      on a float emits the shortest decimal string that parses back to the
//      same double -- not a fixed number of digits.
//
// Detail: a=3 yields values like 13.333333333333334.
//
// This is decidable and tractable when the Python uses a FORMAT SPEC:
// solutions/2496/2496_30.dfy computes in exact rationals and hand-writes
// FormatG9 to replicate '{:.9}'.format(x), and agrees on all 42 comparable
// tests. It is the bare `print(float)` that has no finite specification.
//
// Both gates are therefore inapplicable, not merely failing:
// validate.py and difftest.py both compare stdout as text.
// ===================================================================

