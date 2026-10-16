// `a && b` charges b only when a lets it run; `||` and `==>` likewise.
method Solve(a: seq<int>, i: int) returns (output: bool)
{
  var p := 0 <= i < |a| && a[i] > 0;
  var q := i < 0 || a[i] == 0;
  output := p ==> q;
}
