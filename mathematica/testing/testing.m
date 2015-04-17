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

FactorExpression::usage = ""

Begin["`Private`"] (* Begin Private Context *)

inReals[exp_] := Module[
  {allSymbols, symbols},
  allSymbols = Cases[exp, _Symbol, Infinity];
  symbols = Union[allSymbols];
  Element[symbols, Reals]]

simp[exp_] := Module[
  {assumption},
  assumption = inReals[exp];
  Simplify[exp, assumption]]

commutativeSubsets[exp_] := Module[
  {productQ},
  productQ = Head[exp] === Times && Length[exp] > 2;
  If[productQ,
    Module[{subproductSets, subproducts},
      subproductSets = Subsets[List @@ exp, {2, Infinity}];
      subproducts = Times @@@ subproducts;
      Sow /@ subproducts],
    Sow[exp]];
  Return[exp];
]

factorExp[exp_] := Module[
  {subexpressions, compoundSubexpressions, subexpressionCounts, mostRedundant},
  subexpressions = (First @* Last) @ Reap[Map[commutativeSubsets, exp, Infinity]];
  compoundSubexpressions = Select[subexpressions, Depth[#] > 1 &];
  subexpressionCounts = Tally[compoundSubexpressions];
  mostRedundant = First[MaximalBy[subexpressionCounts, Last]];
  Return[mostRedundant];
]
    SortBy[
      Select[
        (tallyFirstLast @* Reap) @ {f[exp], Map[f, exp, Infinity]},
        Depth[ #1[[1]] ] > 1 &
      ],
      -Last[#1] &
    ]

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

FactorExpression[exp_] := factor[exp]

End[] (* End Private Context *)

EndPackage[]