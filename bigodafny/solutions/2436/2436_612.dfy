// 1111_A. Superhero Transformation  (problem 2436, solution 2436_612)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a={*'aeiou'}
// i=input
// x,y=i(),i()
// print('YNEOS'[len(x)!=len(y) or any((u in a)^(v in a) for u,v in zip(x,y))::2])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

predicate IsVowel612(c: char)
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

method Solve(a: string, b: string) returns (output: string)
{
  if |a| != |b| {
    output := "NO\n";
  } else {
    var i := 0;
    var mismatch := false;
    while i < |a| && !mismatch
      invariant 0 <= i <= |a|
      decreases |a| - i, (if mismatch then 0 else 1)
    {
      if IsVowel612(a[i]) != IsVowel612(b[i]) {
        mismatch := true;
      } else {
        i := i + 1;
      }
    }
    if mismatch {
      output := "NO\n";
    } else {
      output := "YES\n";
    }
  }
}
