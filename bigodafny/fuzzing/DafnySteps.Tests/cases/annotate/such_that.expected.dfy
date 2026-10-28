
method Solve(s: set<int>, a: seq<int>, k: int)
    returns (output: int, ghost steps: nat)
  requires k in a
{
  steps := 0;
  output := 0;
  var left := s;
  while left != {}
    decreases |left|
  {
    steps := steps + 2;
    steps := steps + 1;
    var x :| x in left;
    steps := steps + 1;
    output := output + x;
    steps := steps + 2;
    left := left - {x};
  }
  steps := steps + 1;
  ghost var m :| 0 <= m < |a| && a[m] == k;
  var t := 0;
  while a[t] != k
    invariant 0 <= t <= m
    decreases m - t
  {
    steps := steps + 3;
    steps := steps + 1;
    t := t + 1;
  }
  steps := steps + 2;
}
