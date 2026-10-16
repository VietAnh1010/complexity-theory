// `s + t` charges |t|; a display 1 per element; an update or a slice 1.
method Solve(s: seq<int>, t: seq<int>, x: int) returns (output: seq<int>)
{
  var u := s + t;
  var v := [x, x + 1, 0];
  var w := u[0 := x];
  output := w[1..] + v;
}
