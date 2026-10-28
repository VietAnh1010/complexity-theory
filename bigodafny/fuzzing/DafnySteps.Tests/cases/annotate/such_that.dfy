// `var x :| x in s` charges 1: one step of iterating s. A ghost `:|` charges nothing.
method Solve(s: set<int>, a: seq<int>, k: int) returns (output: int)
  requires k in a
{
  output := 0;
  var left := s;
  while left != {}
    decreases |left|
  {
    var x :| x in left;
    output := output + x;
    left := left - {x};
  }
  ghost var m :| 0 <= m < |a| && a[m] == k;
  var t := 0;
  while a[t] != k
    invariant 0 <= t <= m
    decreases m - t
  {
    t := t + 1;
  }
}
