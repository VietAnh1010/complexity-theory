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

method Solve(n: int) returns (output: string)
{
  var isprime: seq<bool> := seq(2003, _ => true);
  isprime := isprime[0 := false];
  isprime := isprime[1 := false];
  var i := 2;
  while i < 2000
    invariant 2 <= i <= 2000
    invariant |isprime| == 2003
    decreases 2000 - i
  {
    if isprime[i] {
      var j := i * i;
      while j < 2000
        invariant |isprime| == 2003
        decreases 2000 - j
      {
        isprime := isprime[j := false];
        j := j + i;
      }
    }
    i := i + 1;
  }

  var primes: seq<int> := [];
  var k := 2;
  while k < 2000
    invariant 2 <= k <= 2000
    invariant |isprime| == 2003
    decreases 2000 - k
  {
    if isprime[k] {
      primes := primes + [k];
    }
    k := k + 1;
  }

  if n == 2 {
    output := "-1";
  } else {
    var lines: seq<string> := [];
    var ii := 0;
    while ii < n
      invariant 0 <= ii
      decreases n - ii
    {
      var val := 1;
      var jj := 0;
      while jj < n
        invariant 0 <= jj
        decreases n - jj
      {
        if ii != jj && jj < |primes| {
          val := val * primes[jj];
        }
        jj := jj + 1;
      }
      lines := lines + [IntToString(val)];
      ii := ii + 1;
    }
    output := Join(lines, "\n");
  }
}
