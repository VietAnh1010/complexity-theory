// A charge outside the model is 1, with a note.
method Solve(n: nat) returns (output: seq<int>)
{
  var s := seq(n, i => i * 2);
  var t := set x | x in s && x > 0;
  output := s;
}
