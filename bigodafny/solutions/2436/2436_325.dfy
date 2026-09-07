// 1111_A. Superhero Transformation  (problem 2436, solution 2436_325)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// cons=['b', 'c', 'd','f', 'g', 'h', 'j', 'k', 'l', 'm', 'n', 'p', 'q', 'r', 's', 't','v', 'w', 'x', 'y', 'z']
// vow=['a','e','i','o','u']
// a=input()
// b=input()
// n=len(a)
// a=list(a)
// b=list(b)
// i=0
// while(i<n): 
//     if (n!=len(b)):
//         print('No')
//         break
//     if ((a[i] in cons) and (b[i] in vow)) or ((a[i] in vow) and (b[i] in cons)):
//         print("No")
//         break
//     i=i+1
// if (i==n):
//     print("Yes")
// 
//                     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

predicate IsVowel(c: char)
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

predicate IsCons(c: char)
{
  'a' <= c <= 'z' && !IsVowel(c)
}

method Solve(a: string, b: string) returns (output: string)
{
  var n := |a|;
  var i := 0;
  var broke := false;
  while i < n && !broke
    invariant 0 <= i <= n
    decreases n - i, (if broke then 0 else 1)
  {
    if n != |b| {
      broke := true;
    } else if (IsCons(a[i]) && IsVowel(b[i])) || (IsVowel(a[i]) && IsCons(b[i])) {
      broke := true;
    } else {
      i := i + 1;
    }
  }
  if broke {
    output := "No\n";
  } else if i == n {
    output := "Yes\n";
  } else {
    output := "";
  }
}
