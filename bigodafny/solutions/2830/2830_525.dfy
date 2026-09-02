// 746_B. Decoding  (problem 2830, solution 2830_525)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// letras = list(map(str, input()))
// letras_copy = letras.copy()
// index_letras = [i for i in range(n)]
// 
// decoding = []
// 
// while len(letras) != 0:
// 	decoding.append(index_letras[(len(letras)-1)//2])
// 	index_letras.pop((len(letras)-1)//2)
// 	letras.pop((len(letras)-1)//2)
// 
// ans = [(i, l) for i, l in zip(decoding, letras_copy)]
// ans.sort(key=(lambda i: i[0]))
// 
// saida = [l for i, l in ans]
// print(''.join(saida))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  var sz := if n > 0 then n else 0;
  var idxArr := new int[sz];
  var i := 0;
  while i < sz
    invariant 0 <= i <= sz
  {
    idxArr[i] := i;
    i := i + 1;
  }
  var decoding := new int[sz];
  var len := sz;
  var step := 0;
  while len > 0
    invariant 0 <= len <= sz
    invariant 0 <= step <= sz
    invariant step + len == sz
    decreases len
  {
    var pos := (len - 1) / 2;
    decoding[step] := idxArr[pos];
    var j := pos;
    while j < len - 1
      invariant pos <= j <= len - 1
      decreases len - 1 - j
    {
      idxArr[j] := idxArr[j + 1];
      j := j + 1;
    }
    len := len - 1;
    step := step + 1;
  }
  var buf := new char[sz];
  var k := 0;
  while k < sz
    invariant 0 <= k <= sz
  {
    var target := decoding[k];
    if 0 <= target < sz && k < |s| {
      buf[target] := s[k];
    }
    k := k + 1;
  }
  output := buf[0..sz];
}
