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
  output := ""; // TODO: translate the Python above
}
