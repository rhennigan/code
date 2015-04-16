(* Mathematica Package         *)
(* Created by IntelliJ IDEA    *)

(* :Title: testing     *)
(* :Context: testing`  *)
(* :Author: rhennigan            *)
(* :Date: 4/16/2015              *)

(* :Package Version: 1.0       *)
(* :Mathematica Version:       *)
(* :Copyright: (c) 2015 rhennigan *)
(* :Keywords:                  *)
(* :Discussion:                *)

BeginPackage["testing`"]
(* Exported symbols added here with SymbolName::usage *)

Begin["`Private`"] (* Begin Private Context *)

inReals[exp_] := Element[Union[Cases[exp, _Symbol, Infinity]], Reals]

simp[exp_] := Simplify[exp, inReals[exp]]

With[{f = Function[exp, If[Head[exp] === Times && Length[exp] > 2,
  Sow /@ (Times @@@ Subsets[List @@ exp, {2, Infinity}]),
  Sow[exp]
]; exp]},
  factorExp[exp_] :=
      SortBy[Select[
        Tally[First[Last[Reap[{f[exp], Map[f, exp, Infinity]}]]]],
        Depth[#[[1]]] > 1 &], -Last[#] &]
]

ClearAll[factor]
factor[exp_, varCount_] := Module[
  {subexpression, count, newVar, newExp},
  {subexpression, count} = First[factorExp[exp]];
  If[count > 1,
    newVar = Symbol["v" <> ToString[varCount + 1]];
    Sow[{newVar, subexpression}];
    newExp = simp[exp /. subexpression -> newVar];
    factor[newExp, varCount + 1],
    exp
  ]
]
factor[exp_] := Reap[factor[exp, 0]]

End[] (* End Private Context *)

EndPackage[]