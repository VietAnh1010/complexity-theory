// 834_B. The Festive Evening  (problem 1830, solution 1830_0)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// n, k = map(int, input().split())
// a = list(input())
// st = [0] * 26
// ed = [0] * 26
// for i in range(n):
// 	if st[ord(a[i])-65] == 0:
// 		st[ord(a[i])-65] = i + 1
// 	else:
// 		ed[ord(a[i])-65] = i + 1
// for i in range(26):
// 	if st[i] != 0 and ed[i] == 0:
// 		ed[i] = st[i]
// n = 52
// i = 0
// j = 0
// maxi = -1 * sys.maxsize
// l = 0
// st.sort()
// ed.sort()
// while i < 26 and j < 26:
// 	if st[i] == 0:
// 		i += 1
// 		continue
// 	if ed[j] == 0:
// 		j += 1
// 		continue
// 	if st[i] <= ed[j]:
// 		l += 1
// 		i += 1
// 		if l > maxi:
// 			maxi = l
// 	else:
// 		l -= 1
// 		j += 1
// if maxi > k:
// 	print("YES")
// else:
// 	print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, string_: string) returns (output: string)
{
  var st := seq(26, _ => 0);
  var ed := seq(26, _ => 0);
  var idx := 0;
  while idx < n
    decreases n - idx
  {
    var code := string_[idx] as int - 'A' as int;
    if st[code] == 0 {
      st := st[code := idx + 1];
    } else {
      ed := ed[code := idx + 1];
    }
    idx := idx + 1;
  }
  var i := 0;
  while i < 26
    decreases 26 - i
  {
    if st[i] != 0 && ed[i] == 0 {
      ed := ed[i := st[i]];
    }
    i := i + 1;
  }
  st := SortInts(st);
  ed := SortInts(ed);
  var ii := 0;
  var jj := 0;
  var maxi := -1000000000;
  var l := 0;
  while ii < 26 && jj < 26
    decreases (26 - ii) + (26 - jj)
  {
    if st[ii] == 0 {
      ii := ii + 1;
    } else if ed[jj] == 0 {
      jj := jj + 1;
    } else if st[ii] <= ed[jj] {
      l := l + 1;
      ii := ii + 1;
      if l > maxi { maxi := l; }
    } else {
      l := l - 1;
      jj := jj + 1;
    }
  }
  if maxi > k {
    output := "YES";
  } else {
    output := "NO";
  }
}
