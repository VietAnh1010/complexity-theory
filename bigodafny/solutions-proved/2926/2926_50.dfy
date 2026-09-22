// 66_D. Petya and His Friends  (problem 2926, solution 2926_50)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l=[2	,3	,5	,7	,11	,13	,17	,19	,23	,29	,31	,37	,41	,43	,47	,53	,59	,61	,67	,71
// ,73	,79	,83	,89	,97	,101	,103	,107	,109	,113	,127	,131	,137	,139	,149	,151	,157	,163	,167	,173
// ,179	,181	,191	,193	,197	,199	,211	,223	,227	,229	,233	,239	,241]
// n=int(input())
// l1=[1 for i in range(n)]
// if n==2 :
//     print("-1")
//     exit()
// for i in range(n-1) :
//     l1[i]=2*l[i+1]
//     l1[-1]*=l[i+1]
// for x in l1 :
//     print(x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// `primes` is a fixed literal of length 53; the loop below is guarded by
// `i + 1 < |primes|` as well as `i < n - 1`, so it runs at most 52 times
// regardless of n -- a constant, not a value. The dominant cost is building
// and joining `lines`, which is O(n).

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 8 * n + 500
{
  steps := 1;
  var primes := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,
                 73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,
                 179,181,191,193,197,199,211,223,227,229,233,239,241];
  if n == 2 {
    output := "-1\n";
    steps := steps + 1;
  } else if n <= 0 {
    output := "";
    steps := steps + 1;
  } else {
    var l1 := seq(n, _ => 1);
    var last := 1;
    var i := 0;
    ghost var b1 := steps;
    while i < n - 1 && i + 1 < |primes|
      invariant 0 <= i
      invariant i <= 52
      invariant |l1| == n
      invariant steps <= b1 + 4 * i
      decreases 53 - i
    {
      l1 := l1[i := 2 * primes[i+1]];
      last := last * primes[i+1];
      i := i + 1;
      steps := steps + 4;
    }
    l1 := l1[n - 1 := last];
    steps := steps + 3;
    var lines := seq(n, k requires 0 <= k < n => IntToString(l1[k]));
    output := Join(lines, "\n") + "\n";
    steps := steps + 4 * n + 2;
  }
}
