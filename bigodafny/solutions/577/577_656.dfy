// 1345_B. Card Constructions  (problem 577, solution 577_656)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from typing import List
// def pyramid():
//     n = int(input())
//     aux = n
//     respuesta = 1
//     altura = 1
//     if(n<2):
//         respuesta = 0
//     while(aux>=2):
//         aux = aux - 2*altura - altura + 1
//         if( aux < 0 ):
//             aux = aux + 2*altura + altura - 1
//             altura = 1
//             respuesta = respuesta + 1
//         else:
//             altura = altura + 1
//     print(respuesta)
// t = int(input())
// for i in range(t):
//     pyramid()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers_list: seq<int>) returns (output: string)
  requires forall t :: 0 <= t < |numbers_list| ==> numbers_list[t] >= 1
{

  var results: seq<string> := [];
  var i := 0;
  while i < |numbers_list|
    invariant 0 <= i <= |numbers_list|
    decreases |numbers_list| - i
  {
    var r := Pyramid(numbers_list[i]);
    results := results + [IntToString(r)];
    i := i + 1;
  }
  output := Join(results, "\n");
}


method Pyramid(nVal: int) returns (respuesta: int)
  requires nVal >= 0
{
  var aux := nVal;
  respuesta := 1;
  var altura := 1;
  if nVal < 2 { respuesta := 0; }
  while aux >= 2
    invariant aux >= 0
    invariant altura >= 1
    decreases aux, altura
  {
    aux := aux - 2 * altura - altura + 1;
    if aux < 0 {
      aux := aux + 2 * altura + altura - 1;
      altura := 1;
      respuesta := respuesta + 1;
    } else {
      altura := altura + 1;
    }
  }
}
