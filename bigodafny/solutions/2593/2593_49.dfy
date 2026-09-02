// 991_B. Getting an A  (problem 2593, solution 2593_49)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// l = list(map(int,input().split()))
// s = sum(l)
// avg = s/n
// if(avg>=4.5):
//     print(0)
// else:
//     req= s-avg
//     l.sort()
//     i=0
//     while(True):
//        dif = 5-l[i]
//        s =s+dif
//        avg = s/n
//        if(avg>=4.5):
//            print(i+1)
//            break
//        i+=1
//        
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MergeLength<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
  ensures |Merge(a, b, less)| == |a| + |b|
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeLength(a, b[1..], less);
  } else {
    MergeLength(a[1..], b, less);
  }
}

lemma SortLength<T>(s: seq<T>, less: (T, T) -> bool)
  ensures |Sort(s, less)| == |s|
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortLength(s[..|s| / 2], less);
    SortLength(s[|s| / 2..], less);
    MergeLength(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  requires n >= 1
{
  var s := SumSeq(a_list);
  if 2 * s >= 9 * n {
    output := "0";
  } else {
    SortLength(a_list, (x: int, y: int) => x < y);
    var l := SortInts(a_list);
    var i := 0;
    var res := 0;
    var done := false;
    while i < n && !done
      invariant 0 <= i <= n
      invariant |l| == n
      decreases n - i
    {
      var dif := 5 - l[i];
      s := s + dif;
      if 2 * s >= 9 * n {
        res := i + 1;
        done := true;
      }
      i := i + 1;
    }
    output := IntToString(res);
  }
}
