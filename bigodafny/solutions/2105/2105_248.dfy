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
  output := ""; // TODO: translate the Python above
}
