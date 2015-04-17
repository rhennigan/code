(* Mathematica Package              *)
(* Created by IntelliJ IDEA         *)

(* :Title: testing                  *)
(* :Context: testing`               *)
(* :Author: rhennigan               *)
(* :Date: 4/16/2015                 *)

(* :Package Version: 1.0            *)
(* :Mathematica Version:            *)
(* :Copyright: (c) 2015 rhennigan   *)
(* :Keywords:                       *)
(* :Discussion:                     *)

BeginPackage["testing`"]
(* Exported symbols added here with SymbolName::usage *)

(*inReals::usage = ""*)
(*simplify::usage = ""*)
(*commutativeSubsets::usage = ""*)
(*mostRedundantFactor::usage = ""*)
(*factorExpression::usage = ""*)
FactorExpression::usage = ""

Begin["`Private`"] (* Begin Private Context *)

inReals[exp_] := Module[
  {allSymbols, symbols, membership},
  allSymbols = Cases[exp, _Symbol, Infinity];
  symbols = Union[allSymbols];
  membership = Element[symbols, Reals];
  Return[membership];
]

simplify[exp_] := Module[
  {assumption, simplified},
  assumption = inReals[exp];
  simplified = Simplify[exp, assumption];
  Return[simplified];
]

commutativeSubsets[exp_] := Module[
  {productQ},
  productQ = Head[exp] === Times && Length[exp] > 2;
  If[productQ,
    Module[{subproductSets, subproducts},
      subproductSets = Subsets[List @@ exp, {2, Infinity}];
      subproducts = Times @@@ subproducts;
      Sow /@ subproducts
    ],
    Sow[exp]
  ];
  Return[exp];
]

mostRedundantFactor[exp_] := Module[
  {subexpressions, subexpressionCounts, factor, count},
  subexpressions = First @ Last @ Reap[
    commutativeSubsets[exp];
    Map[commutativeSubsets, exp, Infinity]
  ];
  subexpressionCounts = Select[Tally[subexpressions], Depth[ #[[1]] ] > 1 &];
  {factor, count} = First[MaximalBy[subexpressionCounts, Last]];
  Return[{factor, count}];
]

factorExpression[exp_, varCount_Integer] := Module[
  {factor, count},
  {factor, count} = mostRedundantFactor[exp];
  If[count > 1,
    Module[{newVar, newExp},
      (*newVar = Symbol["v" <> ToString[varCount + 1]];*)
      newVar = Module[{v}, v];
      Sow[{newVar, factor}];
      newExp = exp /. factor -> newVar;
      factorExpression[newExp, varCount + 1]
    ],
    exp
  ]
]

FactorExpression[exp_] /; Depth[exp] == 1 := {exp, {}}
FactorExpression[exp_] := Reap[factorExpression[exp, 0]]

End[] (* End Private Context *)

EndPackage[]