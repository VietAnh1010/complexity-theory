// 66_D. Petya and His Friends  (problem 2926, solution 2926_54)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// isprime = [1 for i in range(2003)]
//
// isprime[0] = 0
// isprime[1] = 0
// for i in range(2,2000,1):
//     if(isprime[i]):
//         j = i*i
//         while j < 2000:
//             isprime[j] = 0
//             j += i
//
// prime = []
// for i in range(2,2000,1):
//     if(isprime[i]):
//         prime.append(i)
//
// n = int(input())
// if(n==2):
//     print('-1')
//     exit(0)
//
// for i in range(n):
//     val = 1
//     for j in range(n):
//         if i==j : continue
//         val *= prime[j]
//     print(val)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// The sieve/prime-filter section is bounded by the literal 2000, not by n:
// it contributes a fixed constant to `steps`, independent of the input. The
// n-dependent cost is entirely the final double loop, which is O(n**2).

// Isolated multiplication: (a+1)*c == a*c + c.
lemma MulDistribAdd(a: int, c: int)
  ensures (a + 1) * c == a * c + c
{}

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 6 * n * n + 6 * n + 4500000
{
  steps := 1;
  var isprime: seq<bool> := seq(2003, _ => true);
  isprime := isprime[0 := false];
  isprime := isprime[1 := false];
  steps := steps + 2;

  var i := 2;
  ghost var ibase0 := steps;
  while i < 2000
    invariant 2 <= i <= 2000
    invariant |isprime| == 2003
    invariant steps <= ibase0 + 2010 * (i - 2)
    decreases 2000 - i
  {
    steps := steps + 1;
    if isprime[i] {
      var j := i * i;
      var cnt := 0;
      ghost var jbase := steps;
      while j < 2000
        invariant |isprime| == 2003
        invariant 2 * cnt <= j
        invariant cnt <= 1000
        invariant steps == jbase + 2 * cnt
        decreases 2000 - j
      {
        isprime := isprime[j := false];
        j := j + i;
        cnt := cnt + 1;
        steps := steps + 2;
      }
      assert steps <= jbase + 2000;
    }
    i := i + 1;
    steps := steps + 1;
  }

  var primes: seq<int> := [];
  var k := 2;
  ghost var kbase0 := steps;
  while k < 2000
    invariant 2 <= k <= 2000
    invariant |isprime| == 2003
    invariant steps <= kbase0 + 3 * (k - 2)
    decreases 2000 - k
  {
    steps := steps + 1;
    if isprime[k] {
      primes := primes + [k];
      steps := steps + 1;
    }
    k := k + 1;
    steps := steps + 1;
  }

  if n == 2 {
    output := "-1";
    steps := steps + 1;
  } else {
    var lines: seq<string> := [];
    var ii := 0;
    ghost var iibase := steps;
    while ii < n
      invariant 0 <= ii <= n
      invariant steps <= iibase + (6 * n + 6) * ii
      decreases n - ii
    {
      var val := 1;
      var jj := 0;
      ghost var jjbase := steps;
      while jj < n
        invariant 0 <= jj <= n
        invariant steps == jjbase + 6 * jj
        decreases n - jj
      {
        if ii != jj && jj < |primes| {
          val := val * primes[jj];
        }
        jj := jj + 1;
        steps := steps + 6;
      }
      lines := lines + [IntToString(val)];
      steps := steps + 2;
      ii := ii + 1;
      assert (ii - 1 + 1) * (6 * n + 6) == (ii - 1) * (6 * n + 6) + (6 * n + 6)
        by { MulDistribAdd(ii - 1, 6 * n + 6); }
      steps := steps + 1;
    }
    output := Join(lines, "\n");
    steps := steps + 1;
  }
}
