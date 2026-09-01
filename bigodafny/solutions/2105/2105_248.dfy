// 1138_A. Sushi for Two  (problem 2105, solution 2105_248)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// PZS= list(map(int, input().split()))
// ARREGLODETIPOS= list(map(int, input().split()))
// if ARREGLODETIPOS[PZS[0]-1]==1:
//     ARREGLODETIPOS.append(2)
// elif ARREGLODETIPOS[PZS[0]-1]==2:
//     ARREGLODETIPOS.append(1)
// cont1=0
// cont2=0
// arreglorepetidos=[]
// arregloacomodado=[]
// cont1=1
// cont2=1
// for i in range(PZS[0]):
//     if ARREGLODETIPOS[i]==1:
//         if ARREGLODETIPOS[i+1]==1:
//             cont1+=1
//         elif ARREGLODETIPOS[i+1]==2:
//             arreglorepetidos.append(cont1)
//             #arregloacomodado.append(cont1)
//             cont1=1
//             cont2=1
//     elif ARREGLODETIPOS[i]==2:
//         if ARREGLODETIPOS[i+1]==2:
//             cont2+=1
//         elif ARREGLODETIPOS[i+1]==1:
//             arreglorepetidos.append(cont2)
//             cont1=1
//             cont2=1
// for m in range (len(arreglorepetidos)-1):
//     if arreglorepetidos[m]<=arreglorepetidos[m+1]:
//         arregloacomodado.append(arreglorepetidos[m]*2)
//     else:
//         arregloacomodado.append(arreglorepetidos[m+1]*2)
// arregloacomodado.sort(reverse=True)
// print(arregloacomodado[0])
//  			   	 	   		 	 		 	     	  	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: string) returns (output: string)
{
  var n := v_0;
  var tipos := ParseInts(SplitWs(v_1));
  if tipos[n - 1] == 1 {
    tipos := tipos + [2];
  } else if tipos[n - 1] == 2 {
    tipos := tipos + [1];
  }
  var cont1 := 1;
  var cont2 := 1;
  var arreglorepetidos: seq<int> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    if tipos[i] == 1 {
      if tipos[i + 1] == 1 {
        cont1 := cont1 + 1;
      } else if tipos[i + 1] == 2 {
        arreglorepetidos := arreglorepetidos + [cont1];
        cont1 := 1;
        cont2 := 1;
      }
    } else if tipos[i] == 2 {
      if tipos[i + 1] == 2 {
        cont2 := cont2 + 1;
      } else if tipos[i + 1] == 1 {
        arreglorepetidos := arreglorepetidos + [cont2];
        cont1 := 1;
        cont2 := 1;
      }
    }
    i := i + 1;
  }
  var arregloacomodado: seq<int> := [];
  var m := 0;
  while m < |arreglorepetidos| - 1
    decreases |arreglorepetidos| - 1 - m
  {
    if arreglorepetidos[m] <= arreglorepetidos[m + 1] {
      arregloacomodado := arregloacomodado + [arreglorepetidos[m] * 2];
    } else {
      arregloacomodado := arregloacomodado + [arreglorepetidos[m + 1] * 2];
    }
    m := m + 1;
  }
  var sorted := Sort(arregloacomodado, (x: int, y: int) => x > y);
  output := IntToString(sorted[0]);
}
